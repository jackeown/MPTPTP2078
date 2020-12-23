%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:06 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.23s
% Verified   : 
% Statistics : Number of formulae       :  217 (2381 expanded)
%              Number of clauses        :  114 ( 653 expanded)
%              Number of leaves         :   28 ( 530 expanded)
%              Depth                    :   26
%              Number of atoms          :  567 (6237 expanded)
%              Number of equality atoms :  314 (2703 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f63,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f49,f63])).

fof(f107,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f64])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f122,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f107,f110])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f84,f110])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_enumset1(X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f94,f110,f110])).

fof(f105,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f109,plain,(
    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f121,plain,(
    k1_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) ),
    inference(definition_unfolding,[],[f109,f110,f110])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f117,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f80,f110])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f55,plain,(
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

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f54,f55])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f114,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f126,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f114])).

fof(f127,plain,(
    ! [X4,X0] : r2_hidden(X4,k1_enumset1(X0,X0,X4)) ),
    inference(equality_resolution,[],[f126])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f46])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f106,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f123,plain,(
    v1_funct_2(sK4,k1_enumset1(sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f106,f110])).

fof(f108,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f64])).

fof(f23,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_tarski(X2) = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_tarski(X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_tarski(X2) = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_tarski(X2) = k1_funct_1(sK1(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK1(X0)) = X0
        & v1_funct_1(sK1(X0))
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_tarski(X2) = k1_funct_1(sK1(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK1(X0)) = X0
      & v1_funct_1(sK1(X0))
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f61])).

fof(f103,plain,(
    ! [X2,X0] :
      ( k1_tarski(X2) = k1_funct_1(sK1(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f120,plain,(
    ! [X2,X0] :
      ( k1_enumset1(X2,X2,X2) = k1_funct_1(sK1(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(definition_unfolding,[],[f103,f110])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f93,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f57])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f131,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f78])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f90,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_20,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2069,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2059,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2065,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3938,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2059,c_2065])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2072,plain,
    ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5136,plain,
    ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3938,c_2072])).

cnf(c_29,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_22,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_29,c_22])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_29,c_28,c_22])).

cnf(c_2058,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_2524,plain,
    ( k7_relat_1(sK4,k1_enumset1(sK2,sK2,sK2)) = sK4 ),
    inference(superposition,[status(thm)],[c_2059,c_2058])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2070,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4107,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_3938,c_2070])).

cnf(c_4291,plain,
    ( k9_relat_1(sK4,k1_enumset1(sK2,sK2,sK2)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2524,c_4107])).

cnf(c_5334,plain,
    ( k11_relat_1(sK4,sK2) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_5136,c_4291])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2068,plain,
    ( k11_relat_1(X0,X1) != k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6312,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5334,c_2068])).

cnf(c_1338,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2754,plain,
    ( v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_28,c_40])).

cnf(c_27,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_534,plain,
    ( ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_42])).

cnf(c_535,plain,
    ( ~ v1_relat_1(sK4)
    | k1_enumset1(X0,X0,X0) != k1_relat_1(sK4)
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_2759,plain,
    ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK4)
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2754,c_535])).

cnf(c_5199,plain,
    ( X0 != k2_relat_1(sK4)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(sK4)
    | k1_enumset1(k1_funct_1(sK4,X1),k1_funct_1(sK4,X1),k1_funct_1(sK4,X1)) = X0 ),
    inference(resolution,[status(thm)],[c_1338,c_2759])).

cnf(c_38,negated_conjecture,
    ( k1_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_5512,plain,
    ( k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4)
    | k1_enumset1(sK2,sK2,sK2) != k1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_5199,c_38])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2458,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)))
    | k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_5819,plain,
    ( k1_enumset1(sK2,sK2,sK2) != k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5512,c_40,c_2458])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_5825,plain,
    ( ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),k1_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_5819,c_0])).

cnf(c_13,plain,
    ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2828,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_enumset1(X0,X0,X0),X1) ),
    inference(resolution,[status(thm)],[c_13,c_15])).

cnf(c_5833,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK4))
    | ~ r1_tarski(k1_relat_1(sK4),k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[status(thm)],[c_5825,c_2828])).

cnf(c_5834,plain,
    ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k1_enumset1(sK2,sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5833])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2063,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8448,plain,
    ( k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2059,c_2063])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2064,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8637,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8448,c_2064])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_8640,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8637,c_45])).

cnf(c_2074,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8645,plain,
    ( r1_tarski(k1_relat_1(sK4),k1_enumset1(sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8640,c_2074])).

cnf(c_9774,plain,
    ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6312,c_5834,c_8645])).

cnf(c_9779,plain,
    ( k11_relat_1(sK4,sK2) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2069,c_9774])).

cnf(c_9780,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9779,c_5334])).

cnf(c_2371,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2372,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2371])).

cnf(c_9783,plain,
    ( k2_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9780,c_45,c_2372])).

cnf(c_2062,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6615,plain,
    ( k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2059,c_2062])).

cnf(c_6,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2080,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK4,k1_enumset1(sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_enumset1(sK2,sK2,sK2) != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_41])).

cnf(c_500,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)))
    | ~ r2_hidden(X0,k1_enumset1(sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_39,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_504,plain,
    ( ~ r2_hidden(X0,k1_enumset1(sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_500,c_42,c_40,c_39])).

cnf(c_2057,plain,
    ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_enumset1(X0,X0,X0) = k1_funct_1(sK1(X1),X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2061,plain,
    ( k1_enumset1(X0,X0,X0) = k1_funct_1(sK1(X1),X0)
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2987,plain,
    ( k1_funct_1(sK1(k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4)),k1_funct_1(sK4,X0)) = k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0))
    | r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2057,c_2061])).

cnf(c_3409,plain,
    ( k1_funct_1(sK1(k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4)),k1_funct_1(sK4,sK2)) = k1_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) ),
    inference(superposition,[status(thm)],[c_2080,c_2987])).

cnf(c_6825,plain,
    ( k1_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k1_funct_1(sK1(k2_relat_1(sK4)),k1_funct_1(sK4,sK2)) ),
    inference(demodulation,[status(thm)],[c_6615,c_3409])).

cnf(c_7354,plain,
    ( k9_relat_1(sK4,k1_funct_1(sK1(k2_relat_1(sK4)),k1_funct_1(sK4,sK2))) = k11_relat_1(sK4,k1_funct_1(sK4,sK2)) ),
    inference(superposition,[status(thm)],[c_6825,c_5136])).

cnf(c_9788,plain,
    ( k9_relat_1(sK4,k1_funct_1(sK1(k1_xboole_0),k1_funct_1(sK4,sK2))) = k11_relat_1(sK4,k1_funct_1(sK4,sK2)) ),
    inference(demodulation,[status(thm)],[c_9783,c_7354])).

cnf(c_25,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2067,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5023,plain,
    ( k7_relat_1(sK4,X0) = k1_xboole_0
    | k9_relat_1(sK4,X0) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4107,c_2067])).

cnf(c_5460,plain,
    ( k7_relat_1(sK4,k1_enumset1(sK2,sK2,sK2)) = k1_xboole_0
    | k2_relat_1(sK4) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK4,k1_enumset1(sK2,sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4291,c_5023])).

cnf(c_5478,plain,
    ( k7_relat_1(sK4,k1_enumset1(sK2,sK2,sK2)) = k1_xboole_0
    | k2_relat_1(sK4) != k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5460,c_2524])).

cnf(c_5479,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5478,c_2524])).

cnf(c_5810,plain,
    ( sK4 = k1_xboole_0
    | k2_relat_1(sK4) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5479,c_45,c_2372])).

cnf(c_5811,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5810])).

cnf(c_9797,plain,
    ( sK4 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9783,c_5811])).

cnf(c_9849,plain,
    ( sK4 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9797])).

cnf(c_9939,plain,
    ( k9_relat_1(k1_xboole_0,k1_funct_1(sK1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2))) = k11_relat_1(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_9788,c_9849])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f131])).

cnf(c_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2071,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2741,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2071])).

cnf(c_4096,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2741,c_2070])).

cnf(c_23,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2077,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2807,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2077,c_2058])).

cnf(c_4098,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4096,c_23,c_2807])).

cnf(c_9941,plain,
    ( k11_relat_1(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9939,c_4098])).

cnf(c_20136,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9941,c_2068])).

cnf(c_24,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_20137,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20136,c_24])).

cnf(c_6827,plain,
    ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6615,c_2057])).

cnf(c_7640,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),k2_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2080,c_6827])).

cnf(c_9790,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9783,c_7640])).

cnf(c_9933,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9790,c_9849])).

cnf(c_2361,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2364,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2361])).

cnf(c_2360,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2362,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2360])).

cnf(c_20139,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(grounding,[status(thm)],[c_2364:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(c_20140,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(grounding,[status(thm)],[c_2362:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20137,c_9933,c_20139,c_20140])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:01:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 7.23/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/1.47  
% 7.23/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.23/1.47  
% 7.23/1.47  ------  iProver source info
% 7.23/1.47  
% 7.23/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.23/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.23/1.47  git: non_committed_changes: false
% 7.23/1.47  git: last_make_outside_of_git: false
% 7.23/1.47  
% 7.23/1.47  ------ 
% 7.23/1.47  ------ Parsing...
% 7.23/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.23/1.47  
% 7.23/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.23/1.47  
% 7.23/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.23/1.47  
% 7.23/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.23/1.47  ------ Proving...
% 7.23/1.47  ------ Problem Properties 
% 7.23/1.47  
% 7.23/1.47  
% 7.23/1.47  clauses                                 39
% 7.23/1.47  conjectures                             3
% 7.23/1.47  EPR                                     3
% 7.23/1.47  Horn                                    35
% 7.23/1.47  unary                                   14
% 7.23/1.47  binary                                  13
% 7.23/1.47  lits                                    77
% 7.23/1.47  lits eq                                 36
% 7.23/1.47  fd_pure                                 0
% 7.23/1.47  fd_pseudo                               0
% 7.23/1.47  fd_cond                                 3
% 7.23/1.47  fd_pseudo_cond                          4
% 7.23/1.47  AC symbols                              0
% 7.23/1.47  
% 7.23/1.47  ------ Input Options Time Limit: Unbounded
% 7.23/1.47  
% 7.23/1.47  
% 7.23/1.47  ------ 
% 7.23/1.47  Current options:
% 7.23/1.47  ------ 
% 7.23/1.47  
% 7.23/1.47  
% 7.23/1.47  
% 7.23/1.47  
% 7.23/1.47  ------ Proving...
% 7.23/1.47  
% 7.23/1.47  
% 7.23/1.47  % SZS status Theorem for theBenchmark.p
% 7.23/1.47  
% 7.23/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.23/1.47  
% 7.23/1.47  fof(f13,axiom,(
% 7.23/1.47    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f33,plain,(
% 7.23/1.47    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.23/1.47    inference(ennf_transformation,[],[f13])).
% 7.23/1.47  
% 7.23/1.47  fof(f60,plain,(
% 7.23/1.47    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 7.23/1.47    inference(nnf_transformation,[],[f33])).
% 7.23/1.47  
% 7.23/1.47  fof(f88,plain,(
% 7.23/1.47    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f60])).
% 7.23/1.47  
% 7.23/1.47  fof(f25,conjecture,(
% 7.23/1.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f26,negated_conjecture,(
% 7.23/1.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 7.23/1.47    inference(negated_conjecture,[],[f25])).
% 7.23/1.47  
% 7.23/1.47  fof(f48,plain,(
% 7.23/1.47    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 7.23/1.47    inference(ennf_transformation,[],[f26])).
% 7.23/1.47  
% 7.23/1.47  fof(f49,plain,(
% 7.23/1.47    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 7.23/1.47    inference(flattening,[],[f48])).
% 7.23/1.47  
% 7.23/1.47  fof(f63,plain,(
% 7.23/1.47    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 7.23/1.47    introduced(choice_axiom,[])).
% 7.23/1.47  
% 7.23/1.47  fof(f64,plain,(
% 7.23/1.47    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 7.23/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f49,f63])).
% 7.23/1.47  
% 7.23/1.47  fof(f107,plain,(
% 7.23/1.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 7.23/1.47    inference(cnf_transformation,[],[f64])).
% 7.23/1.47  
% 7.23/1.47  fof(f3,axiom,(
% 7.23/1.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f74,plain,(
% 7.23/1.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f3])).
% 7.23/1.47  
% 7.23/1.47  fof(f4,axiom,(
% 7.23/1.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f75,plain,(
% 7.23/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f4])).
% 7.23/1.47  
% 7.23/1.47  fof(f110,plain,(
% 7.23/1.47    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 7.23/1.47    inference(definition_unfolding,[],[f74,f75])).
% 7.23/1.47  
% 7.23/1.47  fof(f122,plain,(
% 7.23/1.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)))),
% 7.23/1.47    inference(definition_unfolding,[],[f107,f110])).
% 7.23/1.47  
% 7.23/1.47  fof(f18,axiom,(
% 7.23/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f40,plain,(
% 7.23/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.23/1.47    inference(ennf_transformation,[],[f18])).
% 7.23/1.47  
% 7.23/1.47  fof(f95,plain,(
% 7.23/1.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.23/1.47    inference(cnf_transformation,[],[f40])).
% 7.23/1.47  
% 7.23/1.47  fof(f10,axiom,(
% 7.23/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f31,plain,(
% 7.23/1.47    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 7.23/1.47    inference(ennf_transformation,[],[f10])).
% 7.23/1.47  
% 7.23/1.47  fof(f84,plain,(
% 7.23/1.47    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f31])).
% 7.23/1.47  
% 7.23/1.47  fof(f118,plain,(
% 7.23/1.47    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 7.23/1.47    inference(definition_unfolding,[],[f84,f110])).
% 7.23/1.47  
% 7.23/1.47  fof(f19,axiom,(
% 7.23/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f27,plain,(
% 7.23/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.23/1.47    inference(pure_predicate_removal,[],[f19])).
% 7.23/1.47  
% 7.23/1.47  fof(f41,plain,(
% 7.23/1.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.23/1.47    inference(ennf_transformation,[],[f27])).
% 7.23/1.47  
% 7.23/1.47  fof(f96,plain,(
% 7.23/1.47    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.23/1.47    inference(cnf_transformation,[],[f41])).
% 7.23/1.47  
% 7.23/1.47  fof(f14,axiom,(
% 7.23/1.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f34,plain,(
% 7.23/1.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.23/1.47    inference(ennf_transformation,[],[f14])).
% 7.23/1.47  
% 7.23/1.47  fof(f35,plain,(
% 7.23/1.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.23/1.47    inference(flattening,[],[f34])).
% 7.23/1.47  
% 7.23/1.47  fof(f89,plain,(
% 7.23/1.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f35])).
% 7.23/1.47  
% 7.23/1.47  fof(f12,axiom,(
% 7.23/1.47    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f32,plain,(
% 7.23/1.47    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.23/1.47    inference(ennf_transformation,[],[f12])).
% 7.23/1.47  
% 7.23/1.47  fof(f86,plain,(
% 7.23/1.47    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f32])).
% 7.23/1.47  
% 7.23/1.47  fof(f87,plain,(
% 7.23/1.47    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f60])).
% 7.23/1.47  
% 7.23/1.47  fof(f17,axiom,(
% 7.23/1.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f38,plain,(
% 7.23/1.47    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.23/1.47    inference(ennf_transformation,[],[f17])).
% 7.23/1.47  
% 7.23/1.47  fof(f39,plain,(
% 7.23/1.47    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.23/1.47    inference(flattening,[],[f38])).
% 7.23/1.47  
% 7.23/1.47  fof(f94,plain,(
% 7.23/1.47    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f39])).
% 7.23/1.47  
% 7.23/1.47  fof(f119,plain,(
% 7.23/1.47    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_enumset1(X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.23/1.47    inference(definition_unfolding,[],[f94,f110,f110])).
% 7.23/1.47  
% 7.23/1.47  fof(f105,plain,(
% 7.23/1.47    v1_funct_1(sK4)),
% 7.23/1.47    inference(cnf_transformation,[],[f64])).
% 7.23/1.47  
% 7.23/1.47  fof(f109,plain,(
% 7.23/1.47    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)),
% 7.23/1.47    inference(cnf_transformation,[],[f64])).
% 7.23/1.47  
% 7.23/1.47  fof(f121,plain,(
% 7.23/1.47    k1_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4)),
% 7.23/1.47    inference(definition_unfolding,[],[f109,f110,f110])).
% 7.23/1.47  
% 7.23/1.47  fof(f22,axiom,(
% 7.23/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f44,plain,(
% 7.23/1.47    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.23/1.47    inference(ennf_transformation,[],[f22])).
% 7.23/1.47  
% 7.23/1.47  fof(f99,plain,(
% 7.23/1.47    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.23/1.47    inference(cnf_transformation,[],[f44])).
% 7.23/1.47  
% 7.23/1.47  fof(f1,axiom,(
% 7.23/1.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f50,plain,(
% 7.23/1.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.23/1.47    inference(nnf_transformation,[],[f1])).
% 7.23/1.47  
% 7.23/1.47  fof(f51,plain,(
% 7.23/1.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.23/1.47    inference(flattening,[],[f50])).
% 7.23/1.47  
% 7.23/1.47  fof(f67,plain,(
% 7.23/1.47    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f51])).
% 7.23/1.47  
% 7.23/1.47  fof(f7,axiom,(
% 7.23/1.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f28,plain,(
% 7.23/1.47    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 7.23/1.47    inference(ennf_transformation,[],[f7])).
% 7.23/1.47  
% 7.23/1.47  fof(f80,plain,(
% 7.23/1.47    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f28])).
% 7.23/1.47  
% 7.23/1.47  fof(f117,plain,(
% 7.23/1.47    ( ! [X0,X1] : (m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 7.23/1.47    inference(definition_unfolding,[],[f80,f110])).
% 7.23/1.47  
% 7.23/1.47  fof(f8,axiom,(
% 7.23/1.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f59,plain,(
% 7.23/1.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.23/1.47    inference(nnf_transformation,[],[f8])).
% 7.23/1.47  
% 7.23/1.47  fof(f81,plain,(
% 7.23/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.23/1.47    inference(cnf_transformation,[],[f59])).
% 7.23/1.47  
% 7.23/1.47  fof(f21,axiom,(
% 7.23/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f43,plain,(
% 7.23/1.47    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.23/1.47    inference(ennf_transformation,[],[f21])).
% 7.23/1.47  
% 7.23/1.47  fof(f98,plain,(
% 7.23/1.47    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.23/1.47    inference(cnf_transformation,[],[f43])).
% 7.23/1.47  
% 7.23/1.47  fof(f20,axiom,(
% 7.23/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f42,plain,(
% 7.23/1.47    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.23/1.47    inference(ennf_transformation,[],[f20])).
% 7.23/1.47  
% 7.23/1.47  fof(f97,plain,(
% 7.23/1.47    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.23/1.47    inference(cnf_transformation,[],[f42])).
% 7.23/1.47  
% 7.23/1.47  fof(f2,axiom,(
% 7.23/1.47    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f52,plain,(
% 7.23/1.47    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.23/1.47    inference(nnf_transformation,[],[f2])).
% 7.23/1.47  
% 7.23/1.47  fof(f53,plain,(
% 7.23/1.47    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.23/1.47    inference(flattening,[],[f52])).
% 7.23/1.47  
% 7.23/1.47  fof(f54,plain,(
% 7.23/1.47    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.23/1.47    inference(rectify,[],[f53])).
% 7.23/1.47  
% 7.23/1.47  fof(f55,plain,(
% 7.23/1.47    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.23/1.47    introduced(choice_axiom,[])).
% 7.23/1.47  
% 7.23/1.47  fof(f56,plain,(
% 7.23/1.47    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.23/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f54,f55])).
% 7.23/1.47  
% 7.23/1.47  fof(f70,plain,(
% 7.23/1.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.23/1.47    inference(cnf_transformation,[],[f56])).
% 7.23/1.47  
% 7.23/1.47  fof(f114,plain,(
% 7.23/1.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 7.23/1.47    inference(definition_unfolding,[],[f70,f75])).
% 7.23/1.47  
% 7.23/1.47  fof(f126,plain,(
% 7.23/1.47    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k1_enumset1(X0,X0,X4) != X2) )),
% 7.23/1.47    inference(equality_resolution,[],[f114])).
% 7.23/1.47  
% 7.23/1.47  fof(f127,plain,(
% 7.23/1.47    ( ! [X4,X0] : (r2_hidden(X4,k1_enumset1(X0,X0,X4))) )),
% 7.23/1.47    inference(equality_resolution,[],[f126])).
% 7.23/1.47  
% 7.23/1.47  fof(f24,axiom,(
% 7.23/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f46,plain,(
% 7.23/1.47    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.23/1.47    inference(ennf_transformation,[],[f24])).
% 7.23/1.47  
% 7.23/1.47  fof(f47,plain,(
% 7.23/1.47    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.23/1.47    inference(flattening,[],[f46])).
% 7.23/1.47  
% 7.23/1.47  fof(f104,plain,(
% 7.23/1.47    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f47])).
% 7.23/1.47  
% 7.23/1.47  fof(f106,plain,(
% 7.23/1.47    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 7.23/1.47    inference(cnf_transformation,[],[f64])).
% 7.23/1.47  
% 7.23/1.47  fof(f123,plain,(
% 7.23/1.47    v1_funct_2(sK4,k1_enumset1(sK2,sK2,sK2),sK3)),
% 7.23/1.47    inference(definition_unfolding,[],[f106,f110])).
% 7.23/1.47  
% 7.23/1.47  fof(f108,plain,(
% 7.23/1.47    k1_xboole_0 != sK3),
% 7.23/1.47    inference(cnf_transformation,[],[f64])).
% 7.23/1.47  
% 7.23/1.47  fof(f23,axiom,(
% 7.23/1.47    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_tarski(X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f45,plain,(
% 7.23/1.47    ! [X0] : ? [X1] : (! [X2] : (k1_tarski(X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.23/1.47    inference(ennf_transformation,[],[f23])).
% 7.23/1.47  
% 7.23/1.47  fof(f61,plain,(
% 7.23/1.47    ! [X0] : (? [X1] : (! [X2] : (k1_tarski(X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_tarski(X2) = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0))))),
% 7.23/1.47    introduced(choice_axiom,[])).
% 7.23/1.47  
% 7.23/1.47  fof(f62,plain,(
% 7.23/1.47    ! [X0] : (! [X2] : (k1_tarski(X2) = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0)))),
% 7.23/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f61])).
% 7.23/1.47  
% 7.23/1.47  fof(f103,plain,(
% 7.23/1.47    ( ! [X2,X0] : (k1_tarski(X2) = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f62])).
% 7.23/1.47  
% 7.23/1.47  fof(f120,plain,(
% 7.23/1.47    ( ! [X2,X0] : (k1_enumset1(X2,X2,X2) = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) )),
% 7.23/1.47    inference(definition_unfolding,[],[f103,f110])).
% 7.23/1.47  
% 7.23/1.47  fof(f16,axiom,(
% 7.23/1.47    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f36,plain,(
% 7.23/1.47    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.23/1.47    inference(ennf_transformation,[],[f16])).
% 7.23/1.47  
% 7.23/1.47  fof(f37,plain,(
% 7.23/1.47    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.23/1.47    inference(flattening,[],[f36])).
% 7.23/1.47  
% 7.23/1.47  fof(f93,plain,(
% 7.23/1.47    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.23/1.47    inference(cnf_transformation,[],[f37])).
% 7.23/1.47  
% 7.23/1.47  fof(f5,axiom,(
% 7.23/1.47    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f57,plain,(
% 7.23/1.47    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.23/1.47    inference(nnf_transformation,[],[f5])).
% 7.23/1.47  
% 7.23/1.47  fof(f58,plain,(
% 7.23/1.47    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.23/1.47    inference(flattening,[],[f57])).
% 7.23/1.47  
% 7.23/1.47  fof(f78,plain,(
% 7.23/1.47    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 7.23/1.47    inference(cnf_transformation,[],[f58])).
% 7.23/1.47  
% 7.23/1.47  fof(f131,plain,(
% 7.23/1.47    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.23/1.47    inference(equality_resolution,[],[f78])).
% 7.23/1.47  
% 7.23/1.47  fof(f11,axiom,(
% 7.23/1.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f85,plain,(
% 7.23/1.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.23/1.47    inference(cnf_transformation,[],[f11])).
% 7.23/1.47  
% 7.23/1.47  fof(f15,axiom,(
% 7.23/1.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f91,plain,(
% 7.23/1.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 7.23/1.47    inference(cnf_transformation,[],[f15])).
% 7.23/1.47  
% 7.23/1.47  fof(f6,axiom,(
% 7.23/1.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.23/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.23/1.47  
% 7.23/1.47  fof(f79,plain,(
% 7.23/1.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.23/1.47    inference(cnf_transformation,[],[f6])).
% 7.23/1.47  
% 7.23/1.47  fof(f90,plain,(
% 7.23/1.47    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.23/1.47    inference(cnf_transformation,[],[f15])).
% 7.23/1.47  
% 7.23/1.47  cnf(c_20,plain,
% 7.23/1.47      ( r2_hidden(X0,k1_relat_1(X1))
% 7.23/1.47      | ~ v1_relat_1(X1)
% 7.23/1.47      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 7.23/1.47      inference(cnf_transformation,[],[f88]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2069,plain,
% 7.23/1.47      ( k11_relat_1(X0,X1) = k1_xboole_0
% 7.23/1.47      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 7.23/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_40,negated_conjecture,
% 7.23/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) ),
% 7.23/1.47      inference(cnf_transformation,[],[f122]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2059,plain,
% 7.23/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) = iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_28,plain,
% 7.23/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.47      | v1_relat_1(X0) ),
% 7.23/1.47      inference(cnf_transformation,[],[f95]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2065,plain,
% 7.23/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.23/1.47      | v1_relat_1(X0) = iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_3938,plain,
% 7.23/1.47      ( v1_relat_1(sK4) = iProver_top ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_2059,c_2065]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_17,plain,
% 7.23/1.47      ( ~ v1_relat_1(X0)
% 7.23/1.47      | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 7.23/1.47      inference(cnf_transformation,[],[f118]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2072,plain,
% 7.23/1.47      ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
% 7.23/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5136,plain,
% 7.23/1.47      ( k9_relat_1(sK4,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_3938,c_2072]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_29,plain,
% 7.23/1.47      ( v4_relat_1(X0,X1)
% 7.23/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.23/1.47      inference(cnf_transformation,[],[f96]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_22,plain,
% 7.23/1.47      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.23/1.47      inference(cnf_transformation,[],[f89]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_479,plain,
% 7.23/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.47      | ~ v1_relat_1(X0)
% 7.23/1.47      | k7_relat_1(X0,X1) = X0 ),
% 7.23/1.47      inference(resolution,[status(thm)],[c_29,c_22]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_483,plain,
% 7.23/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.47      | k7_relat_1(X0,X1) = X0 ),
% 7.23/1.47      inference(global_propositional_subsumption,
% 7.23/1.47                [status(thm)],
% 7.23/1.47                [c_479,c_29,c_28,c_22]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2058,plain,
% 7.23/1.47      ( k7_relat_1(X0,X1) = X0
% 7.23/1.47      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2524,plain,
% 7.23/1.47      ( k7_relat_1(sK4,k1_enumset1(sK2,sK2,sK2)) = sK4 ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_2059,c_2058]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_19,plain,
% 7.23/1.47      ( ~ v1_relat_1(X0)
% 7.23/1.47      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.23/1.47      inference(cnf_transformation,[],[f86]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2070,plain,
% 7.23/1.47      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.23/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_4107,plain,
% 7.23/1.47      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_3938,c_2070]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_4291,plain,
% 7.23/1.47      ( k9_relat_1(sK4,k1_enumset1(sK2,sK2,sK2)) = k2_relat_1(sK4) ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_2524,c_4107]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5334,plain,
% 7.23/1.47      ( k11_relat_1(sK4,sK2) = k2_relat_1(sK4) ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_5136,c_4291]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_21,plain,
% 7.23/1.47      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.23/1.47      | ~ v1_relat_1(X1)
% 7.23/1.47      | k11_relat_1(X1,X0) != k1_xboole_0 ),
% 7.23/1.47      inference(cnf_transformation,[],[f87]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2068,plain,
% 7.23/1.47      ( k11_relat_1(X0,X1) != k1_xboole_0
% 7.23/1.47      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 7.23/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_6312,plain,
% 7.23/1.47      ( k2_relat_1(sK4) != k1_xboole_0
% 7.23/1.47      | r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top
% 7.23/1.47      | v1_relat_1(sK4) != iProver_top ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_5334,c_2068]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_1338,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2754,plain,
% 7.23/1.47      ( v1_relat_1(sK4) ),
% 7.23/1.47      inference(resolution,[status(thm)],[c_28,c_40]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_27,plain,
% 7.23/1.47      ( ~ v1_funct_1(X0)
% 7.23/1.47      | ~ v1_relat_1(X0)
% 7.23/1.47      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 7.23/1.47      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 7.23/1.47      inference(cnf_transformation,[],[f119]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_42,negated_conjecture,
% 7.23/1.47      ( v1_funct_1(sK4) ),
% 7.23/1.47      inference(cnf_transformation,[],[f105]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_534,plain,
% 7.23/1.47      ( ~ v1_relat_1(X0)
% 7.23/1.47      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 7.23/1.47      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 7.23/1.47      | sK4 != X0 ),
% 7.23/1.47      inference(resolution_lifted,[status(thm)],[c_27,c_42]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_535,plain,
% 7.23/1.47      ( ~ v1_relat_1(sK4)
% 7.23/1.47      | k1_enumset1(X0,X0,X0) != k1_relat_1(sK4)
% 7.23/1.47      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
% 7.23/1.47      inference(unflattening,[status(thm)],[c_534]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2759,plain,
% 7.23/1.47      ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK4)
% 7.23/1.47      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k2_relat_1(sK4) ),
% 7.23/1.47      inference(backward_subsumption_resolution,
% 7.23/1.47                [status(thm)],
% 7.23/1.47                [c_2754,c_535]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5199,plain,
% 7.23/1.47      ( X0 != k2_relat_1(sK4)
% 7.23/1.47      | k1_enumset1(X1,X1,X1) != k1_relat_1(sK4)
% 7.23/1.47      | k1_enumset1(k1_funct_1(sK4,X1),k1_funct_1(sK4,X1),k1_funct_1(sK4,X1)) = X0 ),
% 7.23/1.47      inference(resolution,[status(thm)],[c_1338,c_2759]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_38,negated_conjecture,
% 7.23/1.47      ( k1_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) ),
% 7.23/1.47      inference(cnf_transformation,[],[f121]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5512,plain,
% 7.23/1.47      ( k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4)
% 7.23/1.47      | k1_enumset1(sK2,sK2,sK2) != k1_relat_1(sK4) ),
% 7.23/1.47      inference(resolution,[status(thm)],[c_5199,c_38]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_32,plain,
% 7.23/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.47      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.23/1.47      inference(cnf_transformation,[],[f99]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2458,plain,
% 7.23/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)))
% 7.23/1.47      | k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
% 7.23/1.47      inference(instantiation,[status(thm)],[c_32]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5819,plain,
% 7.23/1.47      ( k1_enumset1(sK2,sK2,sK2) != k1_relat_1(sK4) ),
% 7.23/1.47      inference(global_propositional_subsumption,
% 7.23/1.47                [status(thm)],
% 7.23/1.47                [c_5512,c_40,c_2458]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_0,plain,
% 7.23/1.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.23/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5825,plain,
% 7.23/1.47      ( ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),k1_relat_1(sK4))
% 7.23/1.47      | ~ r1_tarski(k1_relat_1(sK4),k1_enumset1(sK2,sK2,sK2)) ),
% 7.23/1.47      inference(resolution,[status(thm)],[c_5819,c_0]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_13,plain,
% 7.23/1.47      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
% 7.23/1.47      | ~ r2_hidden(X0,X1) ),
% 7.23/1.47      inference(cnf_transformation,[],[f117]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_15,plain,
% 7.23/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.23/1.47      inference(cnf_transformation,[],[f81]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2828,plain,
% 7.23/1.47      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_enumset1(X0,X0,X0),X1) ),
% 7.23/1.47      inference(resolution,[status(thm)],[c_13,c_15]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5833,plain,
% 7.23/1.47      ( ~ r2_hidden(sK2,k1_relat_1(sK4))
% 7.23/1.47      | ~ r1_tarski(k1_relat_1(sK4),k1_enumset1(sK2,sK2,sK2)) ),
% 7.23/1.47      inference(resolution,[status(thm)],[c_5825,c_2828]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5834,plain,
% 7.23/1.47      ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top
% 7.23/1.47      | r1_tarski(k1_relat_1(sK4),k1_enumset1(sK2,sK2,sK2)) != iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_5833]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_31,plain,
% 7.23/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.47      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.23/1.47      inference(cnf_transformation,[],[f98]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2063,plain,
% 7.23/1.47      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.23/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_8448,plain,
% 7.23/1.47      ( k1_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_2059,c_2063]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_30,plain,
% 7.23/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.47      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.23/1.47      inference(cnf_transformation,[],[f97]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2064,plain,
% 7.23/1.47      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.23/1.47      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_8637,plain,
% 7.23/1.47      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = iProver_top
% 7.23/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) != iProver_top ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_8448,c_2064]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_45,plain,
% 7.23/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) = iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_8640,plain,
% 7.23/1.47      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(k1_enumset1(sK2,sK2,sK2))) = iProver_top ),
% 7.23/1.47      inference(global_propositional_subsumption,
% 7.23/1.47                [status(thm)],
% 7.23/1.47                [c_8637,c_45]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2074,plain,
% 7.23/1.47      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.23/1.47      | r1_tarski(X0,X1) = iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_8645,plain,
% 7.23/1.47      ( r1_tarski(k1_relat_1(sK4),k1_enumset1(sK2,sK2,sK2)) = iProver_top ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_8640,c_2074]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_9774,plain,
% 7.23/1.47      ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top ),
% 7.23/1.47      inference(global_propositional_subsumption,
% 7.23/1.47                [status(thm)],
% 7.23/1.47                [c_6312,c_5834,c_8645]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_9779,plain,
% 7.23/1.47      ( k11_relat_1(sK4,sK2) = k1_xboole_0
% 7.23/1.47      | v1_relat_1(sK4) != iProver_top ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_2069,c_9774]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_9780,plain,
% 7.23/1.47      ( k2_relat_1(sK4) = k1_xboole_0 | v1_relat_1(sK4) != iProver_top ),
% 7.23/1.47      inference(demodulation,[status(thm)],[c_9779,c_5334]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2371,plain,
% 7.23/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)))
% 7.23/1.47      | v1_relat_1(sK4) ),
% 7.23/1.47      inference(instantiation,[status(thm)],[c_28]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2372,plain,
% 7.23/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))) != iProver_top
% 7.23/1.47      | v1_relat_1(sK4) = iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_2371]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_9783,plain,
% 7.23/1.47      ( k2_relat_1(sK4) = k1_xboole_0 ),
% 7.23/1.47      inference(global_propositional_subsumption,
% 7.23/1.47                [status(thm)],
% 7.23/1.47                [c_9780,c_45,c_2372]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2062,plain,
% 7.23/1.47      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.23/1.47      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_6615,plain,
% 7.23/1.47      ( k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_2059,c_2062]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_6,plain,
% 7.23/1.47      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) ),
% 7.23/1.47      inference(cnf_transformation,[],[f127]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2080,plain,
% 7.23/1.47      ( r2_hidden(X0,k1_enumset1(X1,X1,X0)) = iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_37,plain,
% 7.23/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.23/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.47      | ~ r2_hidden(X3,X1)
% 7.23/1.47      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 7.23/1.47      | ~ v1_funct_1(X0)
% 7.23/1.47      | k1_xboole_0 = X2 ),
% 7.23/1.47      inference(cnf_transformation,[],[f104]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_41,negated_conjecture,
% 7.23/1.47      ( v1_funct_2(sK4,k1_enumset1(sK2,sK2,sK2),sK3) ),
% 7.23/1.47      inference(cnf_transformation,[],[f123]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_499,plain,
% 7.23/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.23/1.47      | ~ r2_hidden(X3,X1)
% 7.23/1.47      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 7.23/1.47      | ~ v1_funct_1(X0)
% 7.23/1.47      | k1_enumset1(sK2,sK2,sK2) != X1
% 7.23/1.47      | sK3 != X2
% 7.23/1.47      | sK4 != X0
% 7.23/1.47      | k1_xboole_0 = X2 ),
% 7.23/1.47      inference(resolution_lifted,[status(thm)],[c_37,c_41]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_500,plain,
% 7.23/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)))
% 7.23/1.47      | ~ r2_hidden(X0,k1_enumset1(sK2,sK2,sK2))
% 7.23/1.47      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4))
% 7.23/1.47      | ~ v1_funct_1(sK4)
% 7.23/1.47      | k1_xboole_0 = sK3 ),
% 7.23/1.47      inference(unflattening,[status(thm)],[c_499]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_39,negated_conjecture,
% 7.23/1.47      ( k1_xboole_0 != sK3 ),
% 7.23/1.47      inference(cnf_transformation,[],[f108]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_504,plain,
% 7.23/1.47      ( ~ r2_hidden(X0,k1_enumset1(sK2,sK2,sK2))
% 7.23/1.47      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4)) ),
% 7.23/1.47      inference(global_propositional_subsumption,
% 7.23/1.47                [status(thm)],
% 7.23/1.47                [c_500,c_42,c_40,c_39]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2057,plain,
% 7.23/1.47      ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top
% 7.23/1.47      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4)) = iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_33,plain,
% 7.23/1.47      ( ~ r2_hidden(X0,X1)
% 7.23/1.47      | k1_enumset1(X0,X0,X0) = k1_funct_1(sK1(X1),X0) ),
% 7.23/1.47      inference(cnf_transformation,[],[f120]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2061,plain,
% 7.23/1.47      ( k1_enumset1(X0,X0,X0) = k1_funct_1(sK1(X1),X0)
% 7.23/1.47      | r2_hidden(X0,X1) != iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2987,plain,
% 7.23/1.47      ( k1_funct_1(sK1(k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4)),k1_funct_1(sK4,X0)) = k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0))
% 7.23/1.47      | r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_2057,c_2061]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_3409,plain,
% 7.23/1.47      ( k1_funct_1(sK1(k2_relset_1(k1_enumset1(sK2,sK2,sK2),sK3,sK4)),k1_funct_1(sK4,sK2)) = k1_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_2080,c_2987]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_6825,plain,
% 7.23/1.47      ( k1_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k1_funct_1(sK1(k2_relat_1(sK4)),k1_funct_1(sK4,sK2)) ),
% 7.23/1.47      inference(demodulation,[status(thm)],[c_6615,c_3409]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_7354,plain,
% 7.23/1.47      ( k9_relat_1(sK4,k1_funct_1(sK1(k2_relat_1(sK4)),k1_funct_1(sK4,sK2))) = k11_relat_1(sK4,k1_funct_1(sK4,sK2)) ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_6825,c_5136]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_9788,plain,
% 7.23/1.47      ( k9_relat_1(sK4,k1_funct_1(sK1(k1_xboole_0),k1_funct_1(sK4,sK2))) = k11_relat_1(sK4,k1_funct_1(sK4,sK2)) ),
% 7.23/1.47      inference(demodulation,[status(thm)],[c_9783,c_7354]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_25,plain,
% 7.23/1.47      ( ~ v1_relat_1(X0)
% 7.23/1.47      | k2_relat_1(X0) != k1_xboole_0
% 7.23/1.47      | k1_xboole_0 = X0 ),
% 7.23/1.47      inference(cnf_transformation,[],[f93]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2067,plain,
% 7.23/1.47      ( k2_relat_1(X0) != k1_xboole_0
% 7.23/1.47      | k1_xboole_0 = X0
% 7.23/1.47      | v1_relat_1(X0) != iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5023,plain,
% 7.23/1.47      ( k7_relat_1(sK4,X0) = k1_xboole_0
% 7.23/1.47      | k9_relat_1(sK4,X0) != k1_xboole_0
% 7.23/1.47      | v1_relat_1(k7_relat_1(sK4,X0)) != iProver_top ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_4107,c_2067]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5460,plain,
% 7.23/1.47      ( k7_relat_1(sK4,k1_enumset1(sK2,sK2,sK2)) = k1_xboole_0
% 7.23/1.47      | k2_relat_1(sK4) != k1_xboole_0
% 7.23/1.47      | v1_relat_1(k7_relat_1(sK4,k1_enumset1(sK2,sK2,sK2))) != iProver_top ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_4291,c_5023]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5478,plain,
% 7.23/1.47      ( k7_relat_1(sK4,k1_enumset1(sK2,sK2,sK2)) = k1_xboole_0
% 7.23/1.47      | k2_relat_1(sK4) != k1_xboole_0
% 7.23/1.47      | v1_relat_1(sK4) != iProver_top ),
% 7.23/1.47      inference(light_normalisation,[status(thm)],[c_5460,c_2524]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5479,plain,
% 7.23/1.47      ( k2_relat_1(sK4) != k1_xboole_0
% 7.23/1.47      | sK4 = k1_xboole_0
% 7.23/1.47      | v1_relat_1(sK4) != iProver_top ),
% 7.23/1.47      inference(demodulation,[status(thm)],[c_5478,c_2524]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5810,plain,
% 7.23/1.47      ( sK4 = k1_xboole_0 | k2_relat_1(sK4) != k1_xboole_0 ),
% 7.23/1.47      inference(global_propositional_subsumption,
% 7.23/1.47                [status(thm)],
% 7.23/1.47                [c_5479,c_45,c_2372]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_5811,plain,
% 7.23/1.47      ( k2_relat_1(sK4) != k1_xboole_0 | sK4 = k1_xboole_0 ),
% 7.23/1.47      inference(renaming,[status(thm)],[c_5810]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_9797,plain,
% 7.23/1.47      ( sK4 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.23/1.47      inference(demodulation,[status(thm)],[c_9783,c_5811]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_9849,plain,
% 7.23/1.47      ( sK4 = k1_xboole_0 ),
% 7.23/1.47      inference(equality_resolution_simp,[status(thm)],[c_9797]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_9939,plain,
% 7.23/1.47      ( k9_relat_1(k1_xboole_0,k1_funct_1(sK1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2))) = k11_relat_1(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)) ),
% 7.23/1.47      inference(light_normalisation,[status(thm)],[c_9788,c_9849]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_9,plain,
% 7.23/1.47      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.23/1.47      inference(cnf_transformation,[],[f131]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_18,plain,
% 7.23/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.23/1.47      inference(cnf_transformation,[],[f85]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2071,plain,
% 7.23/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2741,plain,
% 7.23/1.47      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_9,c_2071]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_4096,plain,
% 7.23/1.47      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_2741,c_2070]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_23,plain,
% 7.23/1.47      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.23/1.47      inference(cnf_transformation,[],[f91]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_12,plain,
% 7.23/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.23/1.47      inference(cnf_transformation,[],[f79]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2077,plain,
% 7.23/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2807,plain,
% 7.23/1.47      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_2077,c_2058]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_4098,plain,
% 7.23/1.47      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.23/1.47      inference(light_normalisation,[status(thm)],[c_4096,c_23,c_2807]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_9941,plain,
% 7.23/1.47      ( k11_relat_1(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)) = k1_xboole_0 ),
% 7.23/1.47      inference(demodulation,[status(thm)],[c_9939,c_4098]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_20136,plain,
% 7.23/1.47      ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),k1_relat_1(k1_xboole_0)) != iProver_top
% 7.23/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_9941,c_2068]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_24,plain,
% 7.23/1.47      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.23/1.47      inference(cnf_transformation,[],[f90]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_20137,plain,
% 7.23/1.47      ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),k1_xboole_0) != iProver_top
% 7.23/1.47      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.23/1.47      inference(light_normalisation,[status(thm)],[c_20136,c_24]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_6827,plain,
% 7.23/1.47      ( r2_hidden(X0,k1_enumset1(sK2,sK2,sK2)) != iProver_top
% 7.23/1.47      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 7.23/1.47      inference(demodulation,[status(thm)],[c_6615,c_2057]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_7640,plain,
% 7.23/1.47      ( r2_hidden(k1_funct_1(sK4,sK2),k2_relat_1(sK4)) = iProver_top ),
% 7.23/1.47      inference(superposition,[status(thm)],[c_2080,c_6827]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_9790,plain,
% 7.23/1.47      ( r2_hidden(k1_funct_1(sK4,sK2),k1_xboole_0) = iProver_top ),
% 7.23/1.47      inference(demodulation,[status(thm)],[c_9783,c_7640]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_9933,plain,
% 7.23/1.47      ( r2_hidden(k1_funct_1(k1_xboole_0,sK2),k1_xboole_0) = iProver_top ),
% 7.23/1.47      inference(light_normalisation,[status(thm)],[c_9790,c_9849]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2361,plain,
% 7.23/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.23/1.47      inference(instantiation,[status(thm)],[c_12]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2364,plain,
% 7.23/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_2361]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2360,plain,
% 7.23/1.47      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.23/1.47      | v1_relat_1(k1_xboole_0) ),
% 7.23/1.47      inference(instantiation,[status(thm)],[c_28]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_2362,plain,
% 7.23/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.23/1.47      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.23/1.47      inference(predicate_to_equality,[status(thm)],[c_2360]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_20139,plain,
% 7.23/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.23/1.47      inference(grounding,
% 7.23/1.47                [status(thm)],
% 7.23/1.47                [c_2364:[bind(X1,$fot(k1_xboole_0)),
% 7.23/1.47                 bind(X0,$fot(k1_xboole_0))]]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(c_20140,plain,
% 7.23/1.47      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 7.23/1.47      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.23/1.47      inference(grounding,
% 7.23/1.47                [status(thm)],
% 7.23/1.47                [c_2362:[bind(X1,$fot(k1_xboole_0)),
% 7.23/1.47                 bind(X0,$fot(k1_xboole_0))]]) ).
% 7.23/1.47  
% 7.23/1.47  cnf(contradiction,plain,
% 7.23/1.47      ( $false ),
% 7.23/1.47      inference(minisat,[status(thm)],[c_20137,c_9933,c_20139,c_20140]) ).
% 7.23/1.47  
% 7.23/1.47  
% 7.23/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.23/1.47  
% 7.23/1.47  ------                               Statistics
% 7.23/1.47  
% 7.23/1.47  ------ Selected
% 7.23/1.47  
% 7.23/1.47  total_time:                             0.652
% 7.23/1.47  
%------------------------------------------------------------------------------
