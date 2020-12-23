%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:51 EST 2020

% Result     : Theorem 19.18s
% Output     : CNFRefutation 19.18s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 654 expanded)
%              Number of clauses        :   72 ( 177 expanded)
%              Number of leaves         :   20 ( 147 expanded)
%              Depth                    :   32
%              Number of atoms          :  425 (1631 expanded)
%              Number of equality atoms :  216 ( 714 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f23,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f63,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK5),sK6,sK8,sK7),k1_tarski(k1_funct_1(sK8,sK5)))
      & k1_xboole_0 != sK6
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK5),sK6,sK8,sK7),k1_tarski(k1_funct_1(sK8,sK5)))
    & k1_xboole_0 != sK6
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f41,f63])).

fof(f104,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) ),
    inference(cnf_transformation,[],[f64])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f107,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f79,f80])).

fof(f108,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f78,f107])).

fof(f120,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
    inference(definition_unfolding,[],[f104,f108])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f53])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f81,f108,f108])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f73,f107])).

fof(f125,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f113])).

fof(f126,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f125])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f99,f107,f107])).

fof(f103,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f64])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK5),sK6,sK8,sK7),k1_tarski(k1_funct_1(sK8,sK5))) ),
    inference(cnf_transformation,[],[f64])).

fof(f119,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK8,sK7),k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5))) ),
    inference(definition_unfolding,[],[f106,f108,f108])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f91,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_62124,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_441,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_37])).

cnf(c_442,plain,
    ( v4_relat_1(sK8,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_492,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_442])).

cnf(c_493,plain,
    ( r1_tarski(k1_relat_1(sK8),X0)
    | ~ v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_417,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(X0)
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_37])).

cnf(c_418,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_18068,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_18256,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_18068])).

cnf(c_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_18076,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_18319,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18256,c_18076])).

cnf(c_18320,plain,
    ( v1_relat_1(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_18319])).

cnf(c_61983,plain,
    ( r1_tarski(k1_relat_1(sK8),X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_493,c_18320])).

cnf(c_62113,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK8),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61983])).

cnf(c_62398,plain,
    ( r1_tarski(k1_relat_1(sK8),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_62113])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_62126,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_62794,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_relat_1(sK8)
    | k1_relat_1(sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_62398,c_62126])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_62130,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_63265,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | r2_hidden(sK5,k1_relat_1(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_62794,c_62130])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_555,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_38])).

cnf(c_556,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | ~ v1_relat_1(sK8)
    | k2_enumset1(k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X1)) = k9_relat_1(sK8,k2_enumset1(X0,X0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_61988,plain,
    ( ~ r2_hidden(X1,k1_relat_1(sK8))
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | k2_enumset1(k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X1)) = k9_relat_1(sK8,k2_enumset1(X0,X0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_18320])).

cnf(c_61989,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X1,k1_relat_1(sK8))
    | k2_enumset1(k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X1)) = k9_relat_1(sK8,k2_enumset1(X0,X0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_61988])).

cnf(c_62112,plain,
    ( k2_enumset1(k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X1)) = k9_relat_1(sK8,k2_enumset1(X0,X0,X0,X1))
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61989])).

cnf(c_63347,plain,
    ( k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,X0)) = k9_relat_1(sK8,k2_enumset1(sK5,sK5,sK5,X0))
    | k1_relat_1(sK8) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_63265,c_62112])).

cnf(c_63480,plain,
    ( k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5)) = k9_relat_1(sK8,k2_enumset1(sK5,sK5,sK5,sK5))
    | k1_relat_1(sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_63265,c_63347])).

cnf(c_22,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_477,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X1,X3))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_442])).

cnf(c_478,plain,
    ( ~ v1_relat_1(sK8)
    | k7_relat_1(sK8,X0) = sK8
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_61979,plain,
    ( k7_relat_1(sK8,X0) = sK8
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_18320])).

cnf(c_62307,plain,
    ( k7_relat_1(sK8,k2_enumset1(sK5,sK5,sK5,sK5)) = sK8 ),
    inference(equality_resolution,[status(thm)],[c_61979])).

cnf(c_61973,plain,
    ( v1_relat_1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_18320])).

cnf(c_62114,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61973])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_62123,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_62476,plain,
    ( k2_relat_1(k7_relat_1(sK8,X0)) = k9_relat_1(sK8,X0) ),
    inference(superposition,[status(thm)],[c_62114,c_62123])).

cnf(c_62552,plain,
    ( k9_relat_1(sK8,k2_enumset1(sK5,sK5,sK5,sK5)) = k2_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_62307,c_62476])).

cnf(c_63492,plain,
    ( k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5)) = k2_relat_1(sK8)
    | k1_relat_1(sK8) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_63480,c_62552])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_432,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_37])).

cnf(c_433,plain,
    ( k7_relset_1(X0,X1,sK8,X2) = k9_relat_1(sK8,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_62273,plain,
    ( k7_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(equality_resolution,[status(thm)],[c_433])).

cnf(c_35,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK8,sK7),k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_62119,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK8,sK7),k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_62291,plain,
    ( r1_tarski(k9_relat_1(sK8,sK7),k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_62273,c_62119])).

cnf(c_63657,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK8,sK7),k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_63492,c_62291])).

cnf(c_63757,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_62124,c_63657])).

cnf(c_63774,plain,
    ( k1_relat_1(sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_63757,c_18319])).

cnf(c_24,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_62121,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_63877,plain,
    ( k2_relat_1(sK8) = k1_xboole_0
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_63774,c_62121])).

cnf(c_63990,plain,
    ( k2_relat_1(sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_63877,c_18319])).

cnf(c_64032,plain,
    ( r1_tarski(k9_relat_1(sK8,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_63990,c_62124])).

cnf(c_64055,plain,
    ( r1_tarski(k9_relat_1(sK8,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_64032,c_18319])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_62132,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_62134,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_62829,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_62132,c_62134])).

cnf(c_64063,plain,
    ( k9_relat_1(sK8,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_64055,c_62829])).

cnf(c_64262,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_64063,c_62291])).

cnf(c_64355,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_64262,c_62132])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:38:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.18/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.18/3.00  
% 19.18/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.18/3.00  
% 19.18/3.00  ------  iProver source info
% 19.18/3.00  
% 19.18/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.18/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.18/3.00  git: non_committed_changes: false
% 19.18/3.00  git: last_make_outside_of_git: false
% 19.18/3.00  
% 19.18/3.00  ------ 
% 19.18/3.00  ------ Parsing...
% 19.18/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  ------ Proving...
% 19.18/3.00  ------ Problem Properties 
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  clauses                                 35
% 19.18/3.00  conjectures                             3
% 19.18/3.00  EPR                                     6
% 19.18/3.00  Horn                                    29
% 19.18/3.00  unary                                   9
% 19.18/3.00  binary                                  6
% 19.18/3.00  lits                                    87
% 19.18/3.00  lits eq                                 32
% 19.18/3.00  fd_pure                                 0
% 19.18/3.00  fd_pseudo                               0
% 19.18/3.00  fd_cond                                 3
% 19.18/3.00  fd_pseudo_cond                          5
% 19.18/3.00  AC symbols                              0
% 19.18/3.00  
% 19.18/3.00  ------ Input Options Time Limit: Unbounded
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing...
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 19.18/3.00  Current options:
% 19.18/3.00  ------ 
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing...
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing...
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing...
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing...
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing...
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 12 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.18/3.00  
% 19.18/3.00  ------ Proving...
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  % SZS status Theorem for theBenchmark.p
% 19.18/3.00  
% 19.18/3.00   Resolution empty clause
% 19.18/3.00  
% 19.18/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.18/3.00  
% 19.18/3.00  fof(f12,axiom,(
% 19.18/3.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f28,plain,(
% 19.18/3.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 19.18/3.00    inference(ennf_transformation,[],[f12])).
% 19.18/3.00  
% 19.18/3.00  fof(f88,plain,(
% 19.18/3.00    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 19.18/3.00    inference(cnf_transformation,[],[f28])).
% 19.18/3.00  
% 19.18/3.00  fof(f10,axiom,(
% 19.18/3.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f27,plain,(
% 19.18/3.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.18/3.00    inference(ennf_transformation,[],[f10])).
% 19.18/3.00  
% 19.18/3.00  fof(f55,plain,(
% 19.18/3.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 19.18/3.00    inference(nnf_transformation,[],[f27])).
% 19.18/3.00  
% 19.18/3.00  fof(f85,plain,(
% 19.18/3.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.18/3.00    inference(cnf_transformation,[],[f55])).
% 19.18/3.00  
% 19.18/3.00  fof(f19,axiom,(
% 19.18/3.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f24,plain,(
% 19.18/3.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 19.18/3.00    inference(pure_predicate_removal,[],[f19])).
% 19.18/3.00  
% 19.18/3.00  fof(f38,plain,(
% 19.18/3.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.18/3.00    inference(ennf_transformation,[],[f24])).
% 19.18/3.00  
% 19.18/3.00  fof(f101,plain,(
% 19.18/3.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.18/3.00    inference(cnf_transformation,[],[f38])).
% 19.18/3.00  
% 19.18/3.00  fof(f21,conjecture,(
% 19.18/3.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f22,negated_conjecture,(
% 19.18/3.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 19.18/3.00    inference(negated_conjecture,[],[f21])).
% 19.18/3.00  
% 19.18/3.00  fof(f23,plain,(
% 19.18/3.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 19.18/3.00    inference(pure_predicate_removal,[],[f22])).
% 19.18/3.00  
% 19.18/3.00  fof(f40,plain,(
% 19.18/3.00    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 19.18/3.00    inference(ennf_transformation,[],[f23])).
% 19.18/3.00  
% 19.18/3.00  fof(f41,plain,(
% 19.18/3.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 19.18/3.00    inference(flattening,[],[f40])).
% 19.18/3.00  
% 19.18/3.00  fof(f63,plain,(
% 19.18/3.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK5),sK6,sK8,sK7),k1_tarski(k1_funct_1(sK8,sK5))) & k1_xboole_0 != sK6 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_1(sK8))),
% 19.18/3.00    introduced(choice_axiom,[])).
% 19.18/3.00  
% 19.18/3.00  fof(f64,plain,(
% 19.18/3.00    ~r1_tarski(k7_relset_1(k1_tarski(sK5),sK6,sK8,sK7),k1_tarski(k1_funct_1(sK8,sK5))) & k1_xboole_0 != sK6 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6))) & v1_funct_1(sK8)),
% 19.18/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f41,f63])).
% 19.18/3.00  
% 19.18/3.00  fof(f104,plain,(
% 19.18/3.00    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK5),sK6)))),
% 19.18/3.00    inference(cnf_transformation,[],[f64])).
% 19.18/3.00  
% 19.18/3.00  fof(f5,axiom,(
% 19.18/3.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f78,plain,(
% 19.18/3.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.18/3.00    inference(cnf_transformation,[],[f5])).
% 19.18/3.00  
% 19.18/3.00  fof(f6,axiom,(
% 19.18/3.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f79,plain,(
% 19.18/3.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.18/3.00    inference(cnf_transformation,[],[f6])).
% 19.18/3.00  
% 19.18/3.00  fof(f7,axiom,(
% 19.18/3.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f80,plain,(
% 19.18/3.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.18/3.00    inference(cnf_transformation,[],[f7])).
% 19.18/3.00  
% 19.18/3.00  fof(f107,plain,(
% 19.18/3.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.18/3.00    inference(definition_unfolding,[],[f79,f80])).
% 19.18/3.00  
% 19.18/3.00  fof(f108,plain,(
% 19.18/3.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 19.18/3.00    inference(definition_unfolding,[],[f78,f107])).
% 19.18/3.00  
% 19.18/3.00  fof(f120,plain,(
% 19.18/3.00    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)))),
% 19.18/3.00    inference(definition_unfolding,[],[f104,f108])).
% 19.18/3.00  
% 19.18/3.00  fof(f9,axiom,(
% 19.18/3.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f26,plain,(
% 19.18/3.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 19.18/3.00    inference(ennf_transformation,[],[f9])).
% 19.18/3.00  
% 19.18/3.00  fof(f84,plain,(
% 19.18/3.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 19.18/3.00    inference(cnf_transformation,[],[f26])).
% 19.18/3.00  
% 19.18/3.00  fof(f11,axiom,(
% 19.18/3.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f87,plain,(
% 19.18/3.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 19.18/3.00    inference(cnf_transformation,[],[f11])).
% 19.18/3.00  
% 19.18/3.00  fof(f8,axiom,(
% 19.18/3.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f53,plain,(
% 19.18/3.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 19.18/3.00    inference(nnf_transformation,[],[f8])).
% 19.18/3.00  
% 19.18/3.00  fof(f54,plain,(
% 19.18/3.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 19.18/3.00    inference(flattening,[],[f53])).
% 19.18/3.00  
% 19.18/3.00  fof(f81,plain,(
% 19.18/3.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 19.18/3.00    inference(cnf_transformation,[],[f54])).
% 19.18/3.00  
% 19.18/3.00  fof(f117,plain,(
% 19.18/3.00    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 19.18/3.00    inference(definition_unfolding,[],[f81,f108,f108])).
% 19.18/3.00  
% 19.18/3.00  fof(f4,axiom,(
% 19.18/3.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f48,plain,(
% 19.18/3.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 19.18/3.00    inference(nnf_transformation,[],[f4])).
% 19.18/3.00  
% 19.18/3.00  fof(f49,plain,(
% 19.18/3.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 19.18/3.00    inference(flattening,[],[f48])).
% 19.18/3.00  
% 19.18/3.00  fof(f50,plain,(
% 19.18/3.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 19.18/3.00    inference(rectify,[],[f49])).
% 19.18/3.00  
% 19.18/3.00  fof(f51,plain,(
% 19.18/3.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 19.18/3.00    introduced(choice_axiom,[])).
% 19.18/3.00  
% 19.18/3.00  fof(f52,plain,(
% 19.18/3.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 19.18/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).
% 19.18/3.00  
% 19.18/3.00  fof(f73,plain,(
% 19.18/3.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 19.18/3.00    inference(cnf_transformation,[],[f52])).
% 19.18/3.00  
% 19.18/3.00  fof(f113,plain,(
% 19.18/3.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 19.18/3.00    inference(definition_unfolding,[],[f73,f107])).
% 19.18/3.00  
% 19.18/3.00  fof(f125,plain,(
% 19.18/3.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 19.18/3.00    inference(equality_resolution,[],[f113])).
% 19.18/3.00  
% 19.18/3.00  fof(f126,plain,(
% 19.18/3.00    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 19.18/3.00    inference(equality_resolution,[],[f125])).
% 19.18/3.00  
% 19.18/3.00  fof(f17,axiom,(
% 19.18/3.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f35,plain,(
% 19.18/3.00    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 19.18/3.00    inference(ennf_transformation,[],[f17])).
% 19.18/3.00  
% 19.18/3.00  fof(f36,plain,(
% 19.18/3.00    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 19.18/3.00    inference(flattening,[],[f35])).
% 19.18/3.00  
% 19.18/3.00  fof(f99,plain,(
% 19.18/3.00    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.18/3.00    inference(cnf_transformation,[],[f36])).
% 19.18/3.00  
% 19.18/3.00  fof(f118,plain,(
% 19.18/3.00    ( ! [X2,X0,X1] : (k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_enumset1(X0,X0,X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.18/3.00    inference(definition_unfolding,[],[f99,f107,f107])).
% 19.18/3.00  
% 19.18/3.00  fof(f103,plain,(
% 19.18/3.00    v1_funct_1(sK8)),
% 19.18/3.00    inference(cnf_transformation,[],[f64])).
% 19.18/3.00  
% 19.18/3.00  fof(f14,axiom,(
% 19.18/3.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f30,plain,(
% 19.18/3.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 19.18/3.00    inference(ennf_transformation,[],[f14])).
% 19.18/3.00  
% 19.18/3.00  fof(f31,plain,(
% 19.18/3.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.18/3.00    inference(flattening,[],[f30])).
% 19.18/3.00  
% 19.18/3.00  fof(f90,plain,(
% 19.18/3.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.18/3.00    inference(cnf_transformation,[],[f31])).
% 19.18/3.00  
% 19.18/3.00  fof(f13,axiom,(
% 19.18/3.00    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f29,plain,(
% 19.18/3.00    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 19.18/3.00    inference(ennf_transformation,[],[f13])).
% 19.18/3.00  
% 19.18/3.00  fof(f89,plain,(
% 19.18/3.00    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 19.18/3.00    inference(cnf_transformation,[],[f29])).
% 19.18/3.00  
% 19.18/3.00  fof(f20,axiom,(
% 19.18/3.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f39,plain,(
% 19.18/3.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.18/3.00    inference(ennf_transformation,[],[f20])).
% 19.18/3.00  
% 19.18/3.00  fof(f102,plain,(
% 19.18/3.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.18/3.00    inference(cnf_transformation,[],[f39])).
% 19.18/3.00  
% 19.18/3.00  fof(f106,plain,(
% 19.18/3.00    ~r1_tarski(k7_relset_1(k1_tarski(sK5),sK6,sK8,sK7),k1_tarski(k1_funct_1(sK8,sK5)))),
% 19.18/3.00    inference(cnf_transformation,[],[f64])).
% 19.18/3.00  
% 19.18/3.00  fof(f119,plain,(
% 19.18/3.00    ~r1_tarski(k7_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK8,sK7),k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5)))),
% 19.18/3.00    inference(definition_unfolding,[],[f106,f108,f108])).
% 19.18/3.00  
% 19.18/3.00  fof(f15,axiom,(
% 19.18/3.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f32,plain,(
% 19.18/3.00    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 19.18/3.00    inference(ennf_transformation,[],[f15])).
% 19.18/3.00  
% 19.18/3.00  fof(f56,plain,(
% 19.18/3.00    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 19.18/3.00    inference(nnf_transformation,[],[f32])).
% 19.18/3.00  
% 19.18/3.00  fof(f91,plain,(
% 19.18/3.00    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.18/3.00    inference(cnf_transformation,[],[f56])).
% 19.18/3.00  
% 19.18/3.00  fof(f3,axiom,(
% 19.18/3.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f71,plain,(
% 19.18/3.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 19.18/3.00    inference(cnf_transformation,[],[f3])).
% 19.18/3.00  
% 19.18/3.00  fof(f2,axiom,(
% 19.18/3.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.18/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.18/3.00  
% 19.18/3.00  fof(f46,plain,(
% 19.18/3.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.18/3.00    inference(nnf_transformation,[],[f2])).
% 19.18/3.00  
% 19.18/3.00  fof(f47,plain,(
% 19.18/3.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.18/3.00    inference(flattening,[],[f46])).
% 19.18/3.00  
% 19.18/3.00  fof(f70,plain,(
% 19.18/3.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.18/3.00    inference(cnf_transformation,[],[f47])).
% 19.18/3.00  
% 19.18/3.00  cnf(c_20,plain,
% 19.18/3.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 19.18/3.00      inference(cnf_transformation,[],[f88]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62124,plain,
% 19.18/3.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 19.18/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_18,plain,
% 19.18/3.00      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 19.18/3.00      inference(cnf_transformation,[],[f85]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_33,plain,
% 19.18/3.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 19.18/3.00      inference(cnf_transformation,[],[f101]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_37,negated_conjecture,
% 19.18/3.00      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6))) ),
% 19.18/3.00      inference(cnf_transformation,[],[f120]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_441,plain,
% 19.18/3.00      ( v4_relat_1(X0,X1)
% 19.18/3.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 19.18/3.00      | sK8 != X0 ),
% 19.18/3.00      inference(resolution_lifted,[status(thm)],[c_33,c_37]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_442,plain,
% 19.18/3.00      ( v4_relat_1(sK8,X0)
% 19.18/3.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 19.18/3.00      inference(unflattening,[status(thm)],[c_441]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_492,plain,
% 19.18/3.00      ( r1_tarski(k1_relat_1(X0),X1)
% 19.18/3.00      | ~ v1_relat_1(X0)
% 19.18/3.00      | X2 != X1
% 19.18/3.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 19.18/3.00      | sK8 != X0 ),
% 19.18/3.00      inference(resolution_lifted,[status(thm)],[c_18,c_442]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_493,plain,
% 19.18/3.00      ( r1_tarski(k1_relat_1(sK8),X0)
% 19.18/3.00      | ~ v1_relat_1(sK8)
% 19.18/3.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 19.18/3.00      inference(unflattening,[status(thm)],[c_492]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_16,plain,
% 19.18/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 19.18/3.00      inference(cnf_transformation,[],[f84]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_417,plain,
% 19.18/3.00      ( ~ v1_relat_1(X0)
% 19.18/3.00      | v1_relat_1(X1)
% 19.18/3.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(X0)
% 19.18/3.00      | sK8 != X1 ),
% 19.18/3.00      inference(resolution_lifted,[status(thm)],[c_16,c_37]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_418,plain,
% 19.18/3.00      ( ~ v1_relat_1(X0)
% 19.18/3.00      | v1_relat_1(sK8)
% 19.18/3.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(X0) ),
% 19.18/3.00      inference(unflattening,[status(thm)],[c_417]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_18068,plain,
% 19.18/3.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(X0)
% 19.18/3.00      | v1_relat_1(X0) != iProver_top
% 19.18/3.00      | v1_relat_1(sK8) = iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_18256,plain,
% 19.18/3.00      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != iProver_top
% 19.18/3.00      | v1_relat_1(sK8) = iProver_top ),
% 19.18/3.00      inference(equality_resolution,[status(thm)],[c_18068]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_19,plain,
% 19.18/3.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 19.18/3.00      inference(cnf_transformation,[],[f87]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_18076,plain,
% 19.18/3.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_18319,plain,
% 19.18/3.00      ( v1_relat_1(sK8) = iProver_top ),
% 19.18/3.00      inference(forward_subsumption_resolution,[status(thm)],[c_18256,c_18076]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_18320,plain,
% 19.18/3.00      ( v1_relat_1(sK8) ),
% 19.18/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_18319]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_61983,plain,
% 19.18/3.00      ( r1_tarski(k1_relat_1(sK8),X0)
% 19.18/3.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 19.18/3.00      inference(global_propositional_subsumption,[status(thm)],[c_493,c_18320]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62113,plain,
% 19.18/3.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 19.18/3.00      | r1_tarski(k1_relat_1(sK8),X0) = iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_61983]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62398,plain,
% 19.18/3.00      ( r1_tarski(k1_relat_1(sK8),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 19.18/3.00      inference(equality_resolution,[status(thm)],[c_62113]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_15,plain,
% 19.18/3.00      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 19.18/3.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 19.18/3.00      | k1_xboole_0 = X0 ),
% 19.18/3.00      inference(cnf_transformation,[],[f117]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62126,plain,
% 19.18/3.00      ( k2_enumset1(X0,X0,X0,X0) = X1
% 19.18/3.00      | k1_xboole_0 = X1
% 19.18/3.00      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62794,plain,
% 19.18/3.00      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_relat_1(sK8)
% 19.18/3.00      | k1_relat_1(sK8) = k1_xboole_0 ),
% 19.18/3.00      inference(superposition,[status(thm)],[c_62398,c_62126]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_11,plain,
% 19.18/3.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 19.18/3.00      inference(cnf_transformation,[],[f126]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62130,plain,
% 19.18/3.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_63265,plain,
% 19.18/3.00      ( k1_relat_1(sK8) = k1_xboole_0
% 19.18/3.00      | r2_hidden(sK5,k1_relat_1(sK8)) = iProver_top ),
% 19.18/3.00      inference(superposition,[status(thm)],[c_62794,c_62130]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_31,plain,
% 19.18/3.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.18/3.00      | ~ r2_hidden(X2,k1_relat_1(X1))
% 19.18/3.00      | ~ v1_funct_1(X1)
% 19.18/3.00      | ~ v1_relat_1(X1)
% 19.18/3.00      | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0)) ),
% 19.18/3.00      inference(cnf_transformation,[],[f118]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_38,negated_conjecture,
% 19.18/3.00      ( v1_funct_1(sK8) ),
% 19.18/3.00      inference(cnf_transformation,[],[f103]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_555,plain,
% 19.18/3.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 19.18/3.00      | ~ r2_hidden(X2,k1_relat_1(X1))
% 19.18/3.00      | ~ v1_relat_1(X1)
% 19.18/3.00      | k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k2_enumset1(X2,X2,X2,X0))
% 19.18/3.00      | sK8 != X1 ),
% 19.18/3.00      inference(resolution_lifted,[status(thm)],[c_31,c_38]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_556,plain,
% 19.18/3.00      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 19.18/3.00      | ~ r2_hidden(X1,k1_relat_1(sK8))
% 19.18/3.00      | ~ v1_relat_1(sK8)
% 19.18/3.00      | k2_enumset1(k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X1)) = k9_relat_1(sK8,k2_enumset1(X0,X0,X0,X1)) ),
% 19.18/3.00      inference(unflattening,[status(thm)],[c_555]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_61988,plain,
% 19.18/3.00      ( ~ r2_hidden(X1,k1_relat_1(sK8))
% 19.18/3.00      | ~ r2_hidden(X0,k1_relat_1(sK8))
% 19.18/3.00      | k2_enumset1(k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X1)) = k9_relat_1(sK8,k2_enumset1(X0,X0,X0,X1)) ),
% 19.18/3.00      inference(global_propositional_subsumption,[status(thm)],[c_556,c_18320]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_61989,plain,
% 19.18/3.00      ( ~ r2_hidden(X0,k1_relat_1(sK8))
% 19.18/3.00      | ~ r2_hidden(X1,k1_relat_1(sK8))
% 19.18/3.00      | k2_enumset1(k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X1)) = k9_relat_1(sK8,k2_enumset1(X0,X0,X0,X1)) ),
% 19.18/3.00      inference(renaming,[status(thm)],[c_61988]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62112,plain,
% 19.18/3.00      ( k2_enumset1(k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X0),k1_funct_1(sK8,X1)) = k9_relat_1(sK8,k2_enumset1(X0,X0,X0,X1))
% 19.18/3.00      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 19.18/3.00      | r2_hidden(X1,k1_relat_1(sK8)) != iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_61989]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_63347,plain,
% 19.18/3.00      ( k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,X0)) = k9_relat_1(sK8,k2_enumset1(sK5,sK5,sK5,X0))
% 19.18/3.00      | k1_relat_1(sK8) = k1_xboole_0
% 19.18/3.00      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 19.18/3.00      inference(superposition,[status(thm)],[c_63265,c_62112]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_63480,plain,
% 19.18/3.00      ( k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5)) = k9_relat_1(sK8,k2_enumset1(sK5,sK5,sK5,sK5))
% 19.18/3.00      | k1_relat_1(sK8) = k1_xboole_0 ),
% 19.18/3.00      inference(superposition,[status(thm)],[c_63265,c_63347]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_22,plain,
% 19.18/3.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 19.18/3.00      inference(cnf_transformation,[],[f90]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_477,plain,
% 19.18/3.00      ( ~ v1_relat_1(X0)
% 19.18/3.00      | X1 != X2
% 19.18/3.00      | k7_relat_1(X0,X2) = X0
% 19.18/3.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X1,X3))
% 19.18/3.00      | sK8 != X0 ),
% 19.18/3.00      inference(resolution_lifted,[status(thm)],[c_22,c_442]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_478,plain,
% 19.18/3.00      ( ~ v1_relat_1(sK8)
% 19.18/3.00      | k7_relat_1(sK8,X0) = sK8
% 19.18/3.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 19.18/3.00      inference(unflattening,[status(thm)],[c_477]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_61979,plain,
% 19.18/3.00      ( k7_relat_1(sK8,X0) = sK8
% 19.18/3.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 19.18/3.00      inference(global_propositional_subsumption,[status(thm)],[c_478,c_18320]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62307,plain,
% 19.18/3.00      ( k7_relat_1(sK8,k2_enumset1(sK5,sK5,sK5,sK5)) = sK8 ),
% 19.18/3.00      inference(equality_resolution,[status(thm)],[c_61979]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_61973,plain,
% 19.18/3.00      ( v1_relat_1(sK8) ),
% 19.18/3.00      inference(global_propositional_subsumption,[status(thm)],[c_418,c_18320]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62114,plain,
% 19.18/3.00      ( v1_relat_1(sK8) = iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_61973]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_21,plain,
% 19.18/3.00      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 19.18/3.00      inference(cnf_transformation,[],[f89]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62123,plain,
% 19.18/3.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 19.18/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62476,plain,
% 19.18/3.00      ( k2_relat_1(k7_relat_1(sK8,X0)) = k9_relat_1(sK8,X0) ),
% 19.18/3.00      inference(superposition,[status(thm)],[c_62114,c_62123]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62552,plain,
% 19.18/3.00      ( k9_relat_1(sK8,k2_enumset1(sK5,sK5,sK5,sK5)) = k2_relat_1(sK8) ),
% 19.18/3.00      inference(superposition,[status(thm)],[c_62307,c_62476]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_63492,plain,
% 19.18/3.00      ( k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5)) = k2_relat_1(sK8)
% 19.18/3.00      | k1_relat_1(sK8) = k1_xboole_0 ),
% 19.18/3.00      inference(light_normalisation,[status(thm)],[c_63480,c_62552]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_34,plain,
% 19.18/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.18/3.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 19.18/3.00      inference(cnf_transformation,[],[f102]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_432,plain,
% 19.18/3.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 19.18/3.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 19.18/3.00      | sK8 != X2 ),
% 19.18/3.00      inference(resolution_lifted,[status(thm)],[c_34,c_37]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_433,plain,
% 19.18/3.00      ( k7_relset_1(X0,X1,sK8,X2) = k9_relat_1(sK8,X2)
% 19.18/3.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 19.18/3.00      inference(unflattening,[status(thm)],[c_432]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62273,plain,
% 19.18/3.00      ( k7_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 19.18/3.00      inference(equality_resolution,[status(thm)],[c_433]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_35,negated_conjecture,
% 19.18/3.00      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK8,sK7),k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5))) ),
% 19.18/3.00      inference(cnf_transformation,[],[f119]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62119,plain,
% 19.18/3.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK5,sK5,sK5,sK5),sK6,sK8,sK7),k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5))) != iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62291,plain,
% 19.18/3.00      ( r1_tarski(k9_relat_1(sK8,sK7),k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5))) != iProver_top ),
% 19.18/3.00      inference(demodulation,[status(thm)],[c_62273,c_62119]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_63657,plain,
% 19.18/3.00      ( k1_relat_1(sK8) = k1_xboole_0
% 19.18/3.00      | r1_tarski(k9_relat_1(sK8,sK7),k2_relat_1(sK8)) != iProver_top ),
% 19.18/3.00      inference(superposition,[status(thm)],[c_63492,c_62291]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_63757,plain,
% 19.18/3.00      ( k1_relat_1(sK8) = k1_xboole_0 | v1_relat_1(sK8) != iProver_top ),
% 19.18/3.00      inference(superposition,[status(thm)],[c_62124,c_63657]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_63774,plain,
% 19.18/3.00      ( k1_relat_1(sK8) = k1_xboole_0 ),
% 19.18/3.00      inference(global_propositional_subsumption,
% 19.18/3.00                [status(thm)],
% 19.18/3.00                [c_63757,c_18319]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_24,plain,
% 19.18/3.00      ( ~ v1_relat_1(X0)
% 19.18/3.00      | k2_relat_1(X0) = k1_xboole_0
% 19.18/3.00      | k1_relat_1(X0) != k1_xboole_0 ),
% 19.18/3.00      inference(cnf_transformation,[],[f91]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62121,plain,
% 19.18/3.00      ( k2_relat_1(X0) = k1_xboole_0
% 19.18/3.00      | k1_relat_1(X0) != k1_xboole_0
% 19.18/3.00      | v1_relat_1(X0) != iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_63877,plain,
% 19.18/3.00      ( k2_relat_1(sK8) = k1_xboole_0 | v1_relat_1(sK8) != iProver_top ),
% 19.18/3.00      inference(superposition,[status(thm)],[c_63774,c_62121]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_63990,plain,
% 19.18/3.00      ( k2_relat_1(sK8) = k1_xboole_0 ),
% 19.18/3.00      inference(global_propositional_subsumption,
% 19.18/3.00                [status(thm)],
% 19.18/3.00                [c_63877,c_18319]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_64032,plain,
% 19.18/3.00      ( r1_tarski(k9_relat_1(sK8,X0),k1_xboole_0) = iProver_top
% 19.18/3.00      | v1_relat_1(sK8) != iProver_top ),
% 19.18/3.00      inference(superposition,[status(thm)],[c_63990,c_62124]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_64055,plain,
% 19.18/3.00      ( r1_tarski(k9_relat_1(sK8,X0),k1_xboole_0) = iProver_top ),
% 19.18/3.00      inference(global_propositional_subsumption,
% 19.18/3.00                [status(thm)],
% 19.18/3.00                [c_64032,c_18319]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_6,plain,
% 19.18/3.00      ( r1_tarski(k1_xboole_0,X0) ),
% 19.18/3.00      inference(cnf_transformation,[],[f71]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62132,plain,
% 19.18/3.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_3,plain,
% 19.18/3.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 19.18/3.00      inference(cnf_transformation,[],[f70]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62134,plain,
% 19.18/3.00      ( X0 = X1
% 19.18/3.00      | r1_tarski(X0,X1) != iProver_top
% 19.18/3.00      | r1_tarski(X1,X0) != iProver_top ),
% 19.18/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_62829,plain,
% 19.18/3.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 19.18/3.00      inference(superposition,[status(thm)],[c_62132,c_62134]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_64063,plain,
% 19.18/3.00      ( k9_relat_1(sK8,X0) = k1_xboole_0 ),
% 19.18/3.00      inference(superposition,[status(thm)],[c_64055,c_62829]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_64262,plain,
% 19.18/3.00      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5),k1_funct_1(sK8,sK5))) != iProver_top ),
% 19.18/3.00      inference(demodulation,[status(thm)],[c_64063,c_62291]) ).
% 19.18/3.00  
% 19.18/3.00  cnf(c_64355,plain,
% 19.18/3.00      ( $false ),
% 19.18/3.00      inference(forward_subsumption_resolution,[status(thm)],[c_64262,c_62132]) ).
% 19.18/3.00  
% 19.18/3.00  
% 19.18/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.18/3.00  
% 19.18/3.00  ------                               Statistics
% 19.18/3.00  
% 19.18/3.00  ------ Selected
% 19.18/3.00  
% 19.18/3.00  total_time:                             2.055
% 19.18/3.00  
%------------------------------------------------------------------------------
