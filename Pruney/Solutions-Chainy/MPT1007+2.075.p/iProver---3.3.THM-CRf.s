%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:57 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 480 expanded)
%              Number of clauses        :   59 ( 119 expanded)
%              Number of leaves         :   17 ( 107 expanded)
%              Depth                    :   19
%              Number of atoms          :  400 (1669 expanded)
%              Number of equality atoms :  175 ( 633 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f40])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f67,f71])).

fof(f69,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f82,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f76])).

fof(f83,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f82])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f70,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_929,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_932,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1583,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_929,c_932])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_enumset1(sK1,sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_423,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))
    | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_425,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_24,c_23])).

cnf(c_1585,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1583,c_425])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_939,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1652,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1585,c_939])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_335,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_26])).

cnf(c_336,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_928,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_931,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1550,plain,
    ( k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_929,c_931])).

cnf(c_1635,plain,
    ( k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1585,c_1550])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_933,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2064,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1635,c_933])).

cnf(c_1637,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1585,c_929])).

cnf(c_3631,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2064,c_1637])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_936,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3637,plain,
    ( r2_hidden(X0,k2_relat_1(sK3)) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3631,c_936])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | m1_subset_1(k1_funct_1(X0,X2),X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_11])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_309,c_26])).

cnf(c_351,plain,
    ( m1_subset_1(k1_funct_1(sK3,X0),X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_927,plain,
    ( m1_subset_1(k1_funct_1(sK3,X0),X1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_1169,plain,
    ( m1_subset_1(k1_funct_1(sK3,X0),sK2) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_929,c_927])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_937,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2293,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1169,c_937])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1086,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1213,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))
    | ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1086])).

cnf(c_1214,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1213])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1263,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1264,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1263])).

cnf(c_3199,plain,
    ( r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2293,c_29,c_1214,c_1264])).

cnf(c_3200,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3199])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_930,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3208,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3200,c_930])).

cnf(c_4044,plain,
    ( r2_hidden(X0,k2_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3637,c_1652,c_3208])).

cnf(c_4052,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_4044])).

cnf(c_4178,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4052,c_29,c_1214,c_1264])).

cnf(c_4186,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1652,c_4178])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.52/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/0.99  
% 2.52/0.99  ------  iProver source info
% 2.52/0.99  
% 2.52/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.52/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/0.99  git: non_committed_changes: false
% 2.52/0.99  git: last_make_outside_of_git: false
% 2.52/0.99  
% 2.52/0.99  ------ 
% 2.52/0.99  
% 2.52/0.99  ------ Input Options
% 2.52/0.99  
% 2.52/0.99  --out_options                           all
% 2.52/0.99  --tptp_safe_out                         true
% 2.52/0.99  --problem_path                          ""
% 2.52/0.99  --include_path                          ""
% 2.52/0.99  --clausifier                            res/vclausify_rel
% 2.52/0.99  --clausifier_options                    --mode clausify
% 2.52/0.99  --stdin                                 false
% 2.52/0.99  --stats_out                             all
% 2.52/0.99  
% 2.52/0.99  ------ General Options
% 2.52/0.99  
% 2.52/0.99  --fof                                   false
% 2.52/0.99  --time_out_real                         305.
% 2.52/0.99  --time_out_virtual                      -1.
% 2.52/0.99  --symbol_type_check                     false
% 2.52/0.99  --clausify_out                          false
% 2.52/0.99  --sig_cnt_out                           false
% 2.52/0.99  --trig_cnt_out                          false
% 2.52/0.99  --trig_cnt_out_tolerance                1.
% 2.52/0.99  --trig_cnt_out_sk_spl                   false
% 2.52/0.99  --abstr_cl_out                          false
% 2.52/0.99  
% 2.52/0.99  ------ Global Options
% 2.52/0.99  
% 2.52/0.99  --schedule                              default
% 2.52/0.99  --add_important_lit                     false
% 2.52/0.99  --prop_solver_per_cl                    1000
% 2.52/0.99  --min_unsat_core                        false
% 2.52/0.99  --soft_assumptions                      false
% 2.52/0.99  --soft_lemma_size                       3
% 2.52/0.99  --prop_impl_unit_size                   0
% 2.52/0.99  --prop_impl_unit                        []
% 2.52/0.99  --share_sel_clauses                     true
% 2.52/0.99  --reset_solvers                         false
% 2.52/0.99  --bc_imp_inh                            [conj_cone]
% 2.52/0.99  --conj_cone_tolerance                   3.
% 2.52/0.99  --extra_neg_conj                        none
% 2.52/0.99  --large_theory_mode                     true
% 2.52/0.99  --prolific_symb_bound                   200
% 2.52/0.99  --lt_threshold                          2000
% 2.52/0.99  --clause_weak_htbl                      true
% 2.52/0.99  --gc_record_bc_elim                     false
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing Options
% 2.52/0.99  
% 2.52/0.99  --preprocessing_flag                    true
% 2.52/0.99  --time_out_prep_mult                    0.1
% 2.52/0.99  --splitting_mode                        input
% 2.52/0.99  --splitting_grd                         true
% 2.52/0.99  --splitting_cvd                         false
% 2.52/0.99  --splitting_cvd_svl                     false
% 2.52/0.99  --splitting_nvd                         32
% 2.52/0.99  --sub_typing                            true
% 2.52/0.99  --prep_gs_sim                           true
% 2.52/0.99  --prep_unflatten                        true
% 2.52/0.99  --prep_res_sim                          true
% 2.52/0.99  --prep_upred                            true
% 2.52/0.99  --prep_sem_filter                       exhaustive
% 2.52/0.99  --prep_sem_filter_out                   false
% 2.52/0.99  --pred_elim                             true
% 2.52/0.99  --res_sim_input                         true
% 2.52/0.99  --eq_ax_congr_red                       true
% 2.52/0.99  --pure_diseq_elim                       true
% 2.52/0.99  --brand_transform                       false
% 2.52/0.99  --non_eq_to_eq                          false
% 2.52/0.99  --prep_def_merge                        true
% 2.52/0.99  --prep_def_merge_prop_impl              false
% 2.52/0.99  --prep_def_merge_mbd                    true
% 2.52/0.99  --prep_def_merge_tr_red                 false
% 2.52/0.99  --prep_def_merge_tr_cl                  false
% 2.52/0.99  --smt_preprocessing                     true
% 2.52/0.99  --smt_ac_axioms                         fast
% 2.52/0.99  --preprocessed_out                      false
% 2.52/0.99  --preprocessed_stats                    false
% 2.52/0.99  
% 2.52/0.99  ------ Abstraction refinement Options
% 2.52/0.99  
% 2.52/0.99  --abstr_ref                             []
% 2.52/0.99  --abstr_ref_prep                        false
% 2.52/0.99  --abstr_ref_until_sat                   false
% 2.52/0.99  --abstr_ref_sig_restrict                funpre
% 2.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.99  --abstr_ref_under                       []
% 2.52/0.99  
% 2.52/0.99  ------ SAT Options
% 2.52/0.99  
% 2.52/0.99  --sat_mode                              false
% 2.52/0.99  --sat_fm_restart_options                ""
% 2.52/0.99  --sat_gr_def                            false
% 2.52/0.99  --sat_epr_types                         true
% 2.52/0.99  --sat_non_cyclic_types                  false
% 2.52/0.99  --sat_finite_models                     false
% 2.52/0.99  --sat_fm_lemmas                         false
% 2.52/0.99  --sat_fm_prep                           false
% 2.52/0.99  --sat_fm_uc_incr                        true
% 2.52/0.99  --sat_out_model                         small
% 2.52/0.99  --sat_out_clauses                       false
% 2.52/0.99  
% 2.52/0.99  ------ QBF Options
% 2.52/0.99  
% 2.52/0.99  --qbf_mode                              false
% 2.52/0.99  --qbf_elim_univ                         false
% 2.52/0.99  --qbf_dom_inst                          none
% 2.52/0.99  --qbf_dom_pre_inst                      false
% 2.52/0.99  --qbf_sk_in                             false
% 2.52/0.99  --qbf_pred_elim                         true
% 2.52/0.99  --qbf_split                             512
% 2.52/0.99  
% 2.52/0.99  ------ BMC1 Options
% 2.52/0.99  
% 2.52/0.99  --bmc1_incremental                      false
% 2.52/0.99  --bmc1_axioms                           reachable_all
% 2.52/0.99  --bmc1_min_bound                        0
% 2.52/0.99  --bmc1_max_bound                        -1
% 2.52/0.99  --bmc1_max_bound_default                -1
% 2.52/0.99  --bmc1_symbol_reachability              true
% 2.52/0.99  --bmc1_property_lemmas                  false
% 2.52/0.99  --bmc1_k_induction                      false
% 2.52/0.99  --bmc1_non_equiv_states                 false
% 2.52/0.99  --bmc1_deadlock                         false
% 2.52/0.99  --bmc1_ucm                              false
% 2.52/0.99  --bmc1_add_unsat_core                   none
% 2.52/0.99  --bmc1_unsat_core_children              false
% 2.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.99  --bmc1_out_stat                         full
% 2.52/0.99  --bmc1_ground_init                      false
% 2.52/0.99  --bmc1_pre_inst_next_state              false
% 2.52/0.99  --bmc1_pre_inst_state                   false
% 2.52/0.99  --bmc1_pre_inst_reach_state             false
% 2.52/0.99  --bmc1_out_unsat_core                   false
% 2.52/0.99  --bmc1_aig_witness_out                  false
% 2.52/0.99  --bmc1_verbose                          false
% 2.52/0.99  --bmc1_dump_clauses_tptp                false
% 2.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.99  --bmc1_dump_file                        -
% 2.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.99  --bmc1_ucm_extend_mode                  1
% 2.52/0.99  --bmc1_ucm_init_mode                    2
% 2.52/0.99  --bmc1_ucm_cone_mode                    none
% 2.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.99  --bmc1_ucm_relax_model                  4
% 2.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.99  --bmc1_ucm_layered_model                none
% 2.52/0.99  --bmc1_ucm_max_lemma_size               10
% 2.52/0.99  
% 2.52/0.99  ------ AIG Options
% 2.52/0.99  
% 2.52/0.99  --aig_mode                              false
% 2.52/0.99  
% 2.52/0.99  ------ Instantiation Options
% 2.52/0.99  
% 2.52/0.99  --instantiation_flag                    true
% 2.52/0.99  --inst_sos_flag                         false
% 2.52/0.99  --inst_sos_phase                        true
% 2.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.99  --inst_lit_sel_side                     num_symb
% 2.52/0.99  --inst_solver_per_active                1400
% 2.52/0.99  --inst_solver_calls_frac                1.
% 2.52/0.99  --inst_passive_queue_type               priority_queues
% 2.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.99  --inst_passive_queues_freq              [25;2]
% 2.52/0.99  --inst_dismatching                      true
% 2.52/0.99  --inst_eager_unprocessed_to_passive     true
% 2.52/0.99  --inst_prop_sim_given                   true
% 2.52/0.99  --inst_prop_sim_new                     false
% 2.52/0.99  --inst_subs_new                         false
% 2.52/0.99  --inst_eq_res_simp                      false
% 2.52/0.99  --inst_subs_given                       false
% 2.52/0.99  --inst_orphan_elimination               true
% 2.52/0.99  --inst_learning_loop_flag               true
% 2.52/0.99  --inst_learning_start                   3000
% 2.52/0.99  --inst_learning_factor                  2
% 2.52/0.99  --inst_start_prop_sim_after_learn       3
% 2.52/0.99  --inst_sel_renew                        solver
% 2.52/0.99  --inst_lit_activity_flag                true
% 2.52/0.99  --inst_restr_to_given                   false
% 2.52/0.99  --inst_activity_threshold               500
% 2.52/0.99  --inst_out_proof                        true
% 2.52/0.99  
% 2.52/0.99  ------ Resolution Options
% 2.52/0.99  
% 2.52/0.99  --resolution_flag                       true
% 2.52/0.99  --res_lit_sel                           adaptive
% 2.52/0.99  --res_lit_sel_side                      none
% 2.52/0.99  --res_ordering                          kbo
% 2.52/0.99  --res_to_prop_solver                    active
% 2.52/0.99  --res_prop_simpl_new                    false
% 2.52/0.99  --res_prop_simpl_given                  true
% 2.52/0.99  --res_passive_queue_type                priority_queues
% 2.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.99  --res_passive_queues_freq               [15;5]
% 2.52/0.99  --res_forward_subs                      full
% 2.52/0.99  --res_backward_subs                     full
% 2.52/0.99  --res_forward_subs_resolution           true
% 2.52/0.99  --res_backward_subs_resolution          true
% 2.52/0.99  --res_orphan_elimination                true
% 2.52/0.99  --res_time_limit                        2.
% 2.52/0.99  --res_out_proof                         true
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Options
% 2.52/0.99  
% 2.52/0.99  --superposition_flag                    true
% 2.52/0.99  --sup_passive_queue_type                priority_queues
% 2.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.99  --demod_completeness_check              fast
% 2.52/0.99  --demod_use_ground                      true
% 2.52/0.99  --sup_to_prop_solver                    passive
% 2.52/0.99  --sup_prop_simpl_new                    true
% 2.52/0.99  --sup_prop_simpl_given                  true
% 2.52/0.99  --sup_fun_splitting                     false
% 2.52/0.99  --sup_smt_interval                      50000
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Simplification Setup
% 2.52/0.99  
% 2.52/0.99  --sup_indices_passive                   []
% 2.52/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_full_bw                           [BwDemod]
% 2.52/0.99  --sup_immed_triv                        [TrivRules]
% 2.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_immed_bw_main                     []
% 2.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.99  
% 2.52/0.99  ------ Combination Options
% 2.52/0.99  
% 2.52/0.99  --comb_res_mult                         3
% 2.52/0.99  --comb_sup_mult                         2
% 2.52/0.99  --comb_inst_mult                        10
% 2.52/0.99  
% 2.52/0.99  ------ Debug Options
% 2.52/0.99  
% 2.52/0.99  --dbg_backtrace                         false
% 2.52/0.99  --dbg_dump_prop_clauses                 false
% 2.52/0.99  --dbg_dump_prop_clauses_file            -
% 2.52/0.99  --dbg_out_stat                          false
% 2.52/0.99  ------ Parsing...
% 2.52/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.52/0.99  ------ Proving...
% 2.52/0.99  ------ Problem Properties 
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  clauses                                 21
% 2.52/0.99  conjectures                             3
% 2.52/0.99  EPR                                     2
% 2.52/0.99  Horn                                    17
% 2.52/0.99  unary                                   7
% 2.52/0.99  binary                                  3
% 2.52/0.99  lits                                    49
% 2.52/0.99  lits eq                                 18
% 2.52/0.99  fd_pure                                 0
% 2.52/0.99  fd_pseudo                               0
% 2.52/0.99  fd_cond                                 0
% 2.52/0.99  fd_pseudo_cond                          3
% 2.52/0.99  AC symbols                              0
% 2.52/0.99  
% 2.52/0.99  ------ Schedule dynamic 5 is on 
% 2.52/0.99  
% 2.52/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  ------ 
% 2.52/0.99  Current options:
% 2.52/0.99  ------ 
% 2.52/0.99  
% 2.52/0.99  ------ Input Options
% 2.52/0.99  
% 2.52/0.99  --out_options                           all
% 2.52/0.99  --tptp_safe_out                         true
% 2.52/0.99  --problem_path                          ""
% 2.52/0.99  --include_path                          ""
% 2.52/0.99  --clausifier                            res/vclausify_rel
% 2.52/0.99  --clausifier_options                    --mode clausify
% 2.52/0.99  --stdin                                 false
% 2.52/0.99  --stats_out                             all
% 2.52/0.99  
% 2.52/0.99  ------ General Options
% 2.52/0.99  
% 2.52/0.99  --fof                                   false
% 2.52/0.99  --time_out_real                         305.
% 2.52/0.99  --time_out_virtual                      -1.
% 2.52/0.99  --symbol_type_check                     false
% 2.52/0.99  --clausify_out                          false
% 2.52/0.99  --sig_cnt_out                           false
% 2.52/0.99  --trig_cnt_out                          false
% 2.52/0.99  --trig_cnt_out_tolerance                1.
% 2.52/0.99  --trig_cnt_out_sk_spl                   false
% 2.52/0.99  --abstr_cl_out                          false
% 2.52/0.99  
% 2.52/0.99  ------ Global Options
% 2.52/0.99  
% 2.52/0.99  --schedule                              default
% 2.52/0.99  --add_important_lit                     false
% 2.52/0.99  --prop_solver_per_cl                    1000
% 2.52/0.99  --min_unsat_core                        false
% 2.52/0.99  --soft_assumptions                      false
% 2.52/0.99  --soft_lemma_size                       3
% 2.52/0.99  --prop_impl_unit_size                   0
% 2.52/0.99  --prop_impl_unit                        []
% 2.52/0.99  --share_sel_clauses                     true
% 2.52/0.99  --reset_solvers                         false
% 2.52/0.99  --bc_imp_inh                            [conj_cone]
% 2.52/0.99  --conj_cone_tolerance                   3.
% 2.52/0.99  --extra_neg_conj                        none
% 2.52/0.99  --large_theory_mode                     true
% 2.52/0.99  --prolific_symb_bound                   200
% 2.52/0.99  --lt_threshold                          2000
% 2.52/0.99  --clause_weak_htbl                      true
% 2.52/0.99  --gc_record_bc_elim                     false
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing Options
% 2.52/0.99  
% 2.52/0.99  --preprocessing_flag                    true
% 2.52/0.99  --time_out_prep_mult                    0.1
% 2.52/0.99  --splitting_mode                        input
% 2.52/0.99  --splitting_grd                         true
% 2.52/0.99  --splitting_cvd                         false
% 2.52/0.99  --splitting_cvd_svl                     false
% 2.52/0.99  --splitting_nvd                         32
% 2.52/0.99  --sub_typing                            true
% 2.52/0.99  --prep_gs_sim                           true
% 2.52/0.99  --prep_unflatten                        true
% 2.52/0.99  --prep_res_sim                          true
% 2.52/0.99  --prep_upred                            true
% 2.52/0.99  --prep_sem_filter                       exhaustive
% 2.52/0.99  --prep_sem_filter_out                   false
% 2.52/0.99  --pred_elim                             true
% 2.52/0.99  --res_sim_input                         true
% 2.52/0.99  --eq_ax_congr_red                       true
% 2.52/0.99  --pure_diseq_elim                       true
% 2.52/0.99  --brand_transform                       false
% 2.52/0.99  --non_eq_to_eq                          false
% 2.52/0.99  --prep_def_merge                        true
% 2.52/0.99  --prep_def_merge_prop_impl              false
% 2.52/0.99  --prep_def_merge_mbd                    true
% 2.52/0.99  --prep_def_merge_tr_red                 false
% 2.52/0.99  --prep_def_merge_tr_cl                  false
% 2.52/0.99  --smt_preprocessing                     true
% 2.52/0.99  --smt_ac_axioms                         fast
% 2.52/0.99  --preprocessed_out                      false
% 2.52/0.99  --preprocessed_stats                    false
% 2.52/0.99  
% 2.52/0.99  ------ Abstraction refinement Options
% 2.52/0.99  
% 2.52/0.99  --abstr_ref                             []
% 2.52/0.99  --abstr_ref_prep                        false
% 2.52/0.99  --abstr_ref_until_sat                   false
% 2.52/0.99  --abstr_ref_sig_restrict                funpre
% 2.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.99  --abstr_ref_under                       []
% 2.52/0.99  
% 2.52/0.99  ------ SAT Options
% 2.52/0.99  
% 2.52/0.99  --sat_mode                              false
% 2.52/0.99  --sat_fm_restart_options                ""
% 2.52/0.99  --sat_gr_def                            false
% 2.52/0.99  --sat_epr_types                         true
% 2.52/0.99  --sat_non_cyclic_types                  false
% 2.52/0.99  --sat_finite_models                     false
% 2.52/0.99  --sat_fm_lemmas                         false
% 2.52/0.99  --sat_fm_prep                           false
% 2.52/0.99  --sat_fm_uc_incr                        true
% 2.52/0.99  --sat_out_model                         small
% 2.52/0.99  --sat_out_clauses                       false
% 2.52/0.99  
% 2.52/0.99  ------ QBF Options
% 2.52/0.99  
% 2.52/0.99  --qbf_mode                              false
% 2.52/0.99  --qbf_elim_univ                         false
% 2.52/0.99  --qbf_dom_inst                          none
% 2.52/0.99  --qbf_dom_pre_inst                      false
% 2.52/0.99  --qbf_sk_in                             false
% 2.52/0.99  --qbf_pred_elim                         true
% 2.52/0.99  --qbf_split                             512
% 2.52/0.99  
% 2.52/0.99  ------ BMC1 Options
% 2.52/0.99  
% 2.52/0.99  --bmc1_incremental                      false
% 2.52/0.99  --bmc1_axioms                           reachable_all
% 2.52/0.99  --bmc1_min_bound                        0
% 2.52/0.99  --bmc1_max_bound                        -1
% 2.52/0.99  --bmc1_max_bound_default                -1
% 2.52/0.99  --bmc1_symbol_reachability              true
% 2.52/0.99  --bmc1_property_lemmas                  false
% 2.52/0.99  --bmc1_k_induction                      false
% 2.52/0.99  --bmc1_non_equiv_states                 false
% 2.52/0.99  --bmc1_deadlock                         false
% 2.52/0.99  --bmc1_ucm                              false
% 2.52/0.99  --bmc1_add_unsat_core                   none
% 2.52/0.99  --bmc1_unsat_core_children              false
% 2.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.99  --bmc1_out_stat                         full
% 2.52/0.99  --bmc1_ground_init                      false
% 2.52/0.99  --bmc1_pre_inst_next_state              false
% 2.52/0.99  --bmc1_pre_inst_state                   false
% 2.52/0.99  --bmc1_pre_inst_reach_state             false
% 2.52/0.99  --bmc1_out_unsat_core                   false
% 2.52/0.99  --bmc1_aig_witness_out                  false
% 2.52/0.99  --bmc1_verbose                          false
% 2.52/0.99  --bmc1_dump_clauses_tptp                false
% 2.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.99  --bmc1_dump_file                        -
% 2.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.99  --bmc1_ucm_extend_mode                  1
% 2.52/0.99  --bmc1_ucm_init_mode                    2
% 2.52/0.99  --bmc1_ucm_cone_mode                    none
% 2.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.99  --bmc1_ucm_relax_model                  4
% 2.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.99  --bmc1_ucm_layered_model                none
% 2.52/0.99  --bmc1_ucm_max_lemma_size               10
% 2.52/0.99  
% 2.52/0.99  ------ AIG Options
% 2.52/0.99  
% 2.52/0.99  --aig_mode                              false
% 2.52/0.99  
% 2.52/0.99  ------ Instantiation Options
% 2.52/0.99  
% 2.52/0.99  --instantiation_flag                    true
% 2.52/0.99  --inst_sos_flag                         false
% 2.52/0.99  --inst_sos_phase                        true
% 2.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.99  --inst_lit_sel_side                     none
% 2.52/0.99  --inst_solver_per_active                1400
% 2.52/0.99  --inst_solver_calls_frac                1.
% 2.52/0.99  --inst_passive_queue_type               priority_queues
% 2.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.99  --inst_passive_queues_freq              [25;2]
% 2.52/0.99  --inst_dismatching                      true
% 2.52/0.99  --inst_eager_unprocessed_to_passive     true
% 2.52/0.99  --inst_prop_sim_given                   true
% 2.52/0.99  --inst_prop_sim_new                     false
% 2.52/0.99  --inst_subs_new                         false
% 2.52/0.99  --inst_eq_res_simp                      false
% 2.52/0.99  --inst_subs_given                       false
% 2.52/0.99  --inst_orphan_elimination               true
% 2.52/0.99  --inst_learning_loop_flag               true
% 2.52/0.99  --inst_learning_start                   3000
% 2.52/0.99  --inst_learning_factor                  2
% 2.52/0.99  --inst_start_prop_sim_after_learn       3
% 2.52/0.99  --inst_sel_renew                        solver
% 2.52/0.99  --inst_lit_activity_flag                true
% 2.52/0.99  --inst_restr_to_given                   false
% 2.52/0.99  --inst_activity_threshold               500
% 2.52/0.99  --inst_out_proof                        true
% 2.52/0.99  
% 2.52/0.99  ------ Resolution Options
% 2.52/0.99  
% 2.52/0.99  --resolution_flag                       false
% 2.52/0.99  --res_lit_sel                           adaptive
% 2.52/0.99  --res_lit_sel_side                      none
% 2.52/0.99  --res_ordering                          kbo
% 2.52/0.99  --res_to_prop_solver                    active
% 2.52/0.99  --res_prop_simpl_new                    false
% 2.52/0.99  --res_prop_simpl_given                  true
% 2.52/0.99  --res_passive_queue_type                priority_queues
% 2.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.99  --res_passive_queues_freq               [15;5]
% 2.52/0.99  --res_forward_subs                      full
% 2.52/0.99  --res_backward_subs                     full
% 2.52/0.99  --res_forward_subs_resolution           true
% 2.52/0.99  --res_backward_subs_resolution          true
% 2.52/0.99  --res_orphan_elimination                true
% 2.52/0.99  --res_time_limit                        2.
% 2.52/0.99  --res_out_proof                         true
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Options
% 2.52/0.99  
% 2.52/0.99  --superposition_flag                    true
% 2.52/0.99  --sup_passive_queue_type                priority_queues
% 2.52/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.99  --demod_completeness_check              fast
% 2.52/0.99  --demod_use_ground                      true
% 2.52/0.99  --sup_to_prop_solver                    passive
% 2.52/0.99  --sup_prop_simpl_new                    true
% 2.52/0.99  --sup_prop_simpl_given                  true
% 2.52/0.99  --sup_fun_splitting                     false
% 2.52/0.99  --sup_smt_interval                      50000
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Simplification Setup
% 2.52/0.99  
% 2.52/0.99  --sup_indices_passive                   []
% 2.52/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_full_bw                           [BwDemod]
% 2.52/0.99  --sup_immed_triv                        [TrivRules]
% 2.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_immed_bw_main                     []
% 2.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.99  
% 2.52/0.99  ------ Combination Options
% 2.52/0.99  
% 2.52/0.99  --comb_res_mult                         3
% 2.52/0.99  --comb_sup_mult                         2
% 2.52/0.99  --comb_inst_mult                        10
% 2.52/0.99  
% 2.52/0.99  ------ Debug Options
% 2.52/0.99  
% 2.52/0.99  --dbg_backtrace                         false
% 2.52/0.99  --dbg_dump_prop_clauses                 false
% 2.52/0.99  --dbg_dump_prop_clauses_file            -
% 2.52/0.99  --dbg_out_stat                          false
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  ------ Proving...
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  % SZS status Theorem for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99   Resolution empty clause
% 2.52/0.99  
% 2.52/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  fof(f15,conjecture,(
% 2.52/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f16,negated_conjecture,(
% 2.52/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.52/0.99    inference(negated_conjecture,[],[f15])).
% 2.52/0.99  
% 2.52/0.99  fof(f32,plain,(
% 2.52/0.99    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.52/0.99    inference(ennf_transformation,[],[f16])).
% 2.52/0.99  
% 2.52/0.99  fof(f33,plain,(
% 2.52/0.99    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.52/0.99    inference(flattening,[],[f32])).
% 2.52/0.99  
% 2.52/0.99  fof(f40,plain,(
% 2.52/0.99    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f41,plain,(
% 2.52/0.99    ~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 2.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f40])).
% 2.52/0.99  
% 2.52/0.99  fof(f68,plain,(
% 2.52/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.52/0.99    inference(cnf_transformation,[],[f41])).
% 2.52/0.99  
% 2.52/0.99  fof(f2,axiom,(
% 2.52/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f48,plain,(
% 2.52/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f2])).
% 2.52/0.99  
% 2.52/0.99  fof(f3,axiom,(
% 2.52/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f49,plain,(
% 2.52/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f3])).
% 2.52/0.99  
% 2.52/0.99  fof(f71,plain,(
% 2.52/0.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.52/0.99    inference(definition_unfolding,[],[f48,f49])).
% 2.52/0.99  
% 2.52/0.99  fof(f78,plain,(
% 2.52/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))),
% 2.52/0.99    inference(definition_unfolding,[],[f68,f71])).
% 2.52/0.99  
% 2.52/0.99  fof(f12,axiom,(
% 2.52/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f28,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(ennf_transformation,[],[f12])).
% 2.52/0.99  
% 2.52/0.99  fof(f58,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f28])).
% 2.52/0.99  
% 2.52/0.99  fof(f14,axiom,(
% 2.52/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f30,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(ennf_transformation,[],[f14])).
% 2.52/0.99  
% 2.52/0.99  fof(f31,plain,(
% 2.52/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(flattening,[],[f30])).
% 2.52/0.99  
% 2.52/0.99  fof(f39,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(nnf_transformation,[],[f31])).
% 2.52/0.99  
% 2.52/0.99  fof(f60,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f39])).
% 2.52/0.99  
% 2.52/0.99  fof(f67,plain,(
% 2.52/0.99    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 2.52/0.99    inference(cnf_transformation,[],[f41])).
% 2.52/0.99  
% 2.52/0.99  fof(f79,plain,(
% 2.52/0.99    v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2)),
% 2.52/0.99    inference(definition_unfolding,[],[f67,f71])).
% 2.52/0.99  
% 2.52/0.99  fof(f69,plain,(
% 2.52/0.99    k1_xboole_0 != sK2),
% 2.52/0.99    inference(cnf_transformation,[],[f41])).
% 2.52/0.99  
% 2.52/0.99  fof(f1,axiom,(
% 2.52/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f34,plain,(
% 2.52/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.52/0.99    inference(nnf_transformation,[],[f1])).
% 2.52/0.99  
% 2.52/0.99  fof(f35,plain,(
% 2.52/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 2.52/0.99    inference(flattening,[],[f34])).
% 2.52/0.99  
% 2.52/0.99  fof(f36,plain,(
% 2.52/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.52/0.99    inference(rectify,[],[f35])).
% 2.52/0.99  
% 2.52/0.99  fof(f37,plain,(
% 2.52/0.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f38,plain,(
% 2.52/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 2.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 2.52/0.99  
% 2.52/0.99  fof(f43,plain,(
% 2.52/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 2.52/0.99    inference(cnf_transformation,[],[f38])).
% 2.52/0.99  
% 2.52/0.99  fof(f76,plain,(
% 2.52/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 2.52/0.99    inference(definition_unfolding,[],[f43,f49])).
% 2.52/0.99  
% 2.52/0.99  fof(f82,plain,(
% 2.52/0.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 2.52/0.99    inference(equality_resolution,[],[f76])).
% 2.52/0.99  
% 2.52/0.99  fof(f83,plain,(
% 2.52/0.99    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 2.52/0.99    inference(equality_resolution,[],[f82])).
% 2.52/0.99  
% 2.52/0.99  fof(f8,axiom,(
% 2.52/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f22,plain,(
% 2.52/0.99    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.52/0.99    inference(ennf_transformation,[],[f8])).
% 2.52/0.99  
% 2.52/0.99  fof(f23,plain,(
% 2.52/0.99    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.52/0.99    inference(flattening,[],[f22])).
% 2.52/0.99  
% 2.52/0.99  fof(f54,plain,(
% 2.52/0.99    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f23])).
% 2.52/0.99  
% 2.52/0.99  fof(f66,plain,(
% 2.52/0.99    v1_funct_1(sK3)),
% 2.52/0.99    inference(cnf_transformation,[],[f41])).
% 2.52/0.99  
% 2.52/0.99  fof(f13,axiom,(
% 2.52/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f29,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(ennf_transformation,[],[f13])).
% 2.52/0.99  
% 2.52/0.99  fof(f59,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f29])).
% 2.52/0.99  
% 2.52/0.99  fof(f11,axiom,(
% 2.52/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f27,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(ennf_transformation,[],[f11])).
% 2.52/0.99  
% 2.52/0.99  fof(f57,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f27])).
% 2.52/0.99  
% 2.52/0.99  fof(f5,axiom,(
% 2.52/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f20,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.52/0.99    inference(ennf_transformation,[],[f5])).
% 2.52/0.99  
% 2.52/0.99  fof(f51,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f20])).
% 2.52/0.99  
% 2.52/0.99  fof(f10,axiom,(
% 2.52/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f17,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.52/0.99    inference(pure_predicate_removal,[],[f10])).
% 2.52/0.99  
% 2.52/0.99  fof(f26,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.52/0.99    inference(ennf_transformation,[],[f17])).
% 2.52/0.99  
% 2.52/0.99  fof(f56,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f26])).
% 2.52/0.99  
% 2.52/0.99  fof(f9,axiom,(
% 2.52/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f24,plain,(
% 2.52/0.99    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 2.52/0.99    inference(ennf_transformation,[],[f9])).
% 2.52/0.99  
% 2.52/0.99  fof(f25,plain,(
% 2.52/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 2.52/0.99    inference(flattening,[],[f24])).
% 2.52/0.99  
% 2.52/0.99  fof(f55,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f25])).
% 2.52/0.99  
% 2.52/0.99  fof(f4,axiom,(
% 2.52/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f18,plain,(
% 2.52/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.52/0.99    inference(ennf_transformation,[],[f4])).
% 2.52/0.99  
% 2.52/0.99  fof(f19,plain,(
% 2.52/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.52/0.99    inference(flattening,[],[f18])).
% 2.52/0.99  
% 2.52/0.99  fof(f50,plain,(
% 2.52/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f19])).
% 2.52/0.99  
% 2.52/0.99  fof(f6,axiom,(
% 2.52/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f21,plain,(
% 2.52/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.52/0.99    inference(ennf_transformation,[],[f6])).
% 2.52/0.99  
% 2.52/0.99  fof(f52,plain,(
% 2.52/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f21])).
% 2.52/0.99  
% 2.52/0.99  fof(f7,axiom,(
% 2.52/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.52/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f53,plain,(
% 2.52/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f7])).
% 2.52/0.99  
% 2.52/0.99  fof(f70,plain,(
% 2.52/0.99    ~r2_hidden(k1_funct_1(sK3,sK1),sK2)),
% 2.52/0.99    inference(cnf_transformation,[],[f41])).
% 2.52/0.99  
% 2.52/0.99  cnf(c_24,negated_conjecture,
% 2.52/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
% 2.52/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_929,plain,
% 2.52/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_14,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_932,plain,
% 2.52/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.52/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1583,plain,
% 2.52/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_relat_1(sK3) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_929,c_932]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_21,plain,
% 2.52/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.52/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.52/0.99      | k1_xboole_0 = X2 ),
% 2.52/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_25,negated_conjecture,
% 2.52/0.99      ( v1_funct_2(sK3,k1_enumset1(sK1,sK1,sK1),sK2) ),
% 2.52/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_422,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.52/0.99      | k1_enumset1(sK1,sK1,sK1) != X1
% 2.52/0.99      | sK2 != X2
% 2.52/0.99      | sK3 != X0
% 2.52/0.99      | k1_xboole_0 = X2 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_423,plain,
% 2.52/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))
% 2.52/0.99      | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1)
% 2.52/0.99      | k1_xboole_0 = sK2 ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_422]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_23,negated_conjecture,
% 2.52/0.99      ( k1_xboole_0 != sK2 ),
% 2.52/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_425,plain,
% 2.52/0.99      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k1_enumset1(sK1,sK1,sK1) ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_423,c_24,c_23]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1585,plain,
% 2.52/0.99      ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK3) ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_1583,c_425]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_4,plain,
% 2.52/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 2.52/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_939,plain,
% 2.52/0.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1652,plain,
% 2.52/0.99      ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_1585,c_939]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_10,plain,
% 2.52/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.52/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.52/0.99      | ~ v1_funct_1(X1)
% 2.52/0.99      | ~ v1_relat_1(X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_26,negated_conjecture,
% 2.52/0.99      ( v1_funct_1(sK3) ),
% 2.52/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_335,plain,
% 2.52/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.52/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.52/0.99      | ~ v1_relat_1(X1)
% 2.52/0.99      | sK3 != X1 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_26]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_336,plain,
% 2.52/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.52/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
% 2.52/0.99      | ~ v1_relat_1(sK3) ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_335]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_928,plain,
% 2.52/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.52/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
% 2.52/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_15,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_931,plain,
% 2.52/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.52/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1550,plain,
% 2.52/0.99      ( k2_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_929,c_931]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1635,plain,
% 2.52/0.99      ( k2_relset_1(k1_relat_1(sK3),sK2,sK3) = k2_relat_1(sK3) ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_1585,c_1550]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_13,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.52/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_933,plain,
% 2.52/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.52/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2064,plain,
% 2.52/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 2.52/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) != iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_1635,c_933]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1637,plain,
% 2.52/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) = iProver_top ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_1585,c_929]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3631,plain,
% 2.52/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.52/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2064,c_1637]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_7,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.52/0.99      | ~ r2_hidden(X2,X0)
% 2.52/0.99      | ~ v1_xboole_0(X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_936,plain,
% 2.52/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.52/0.99      | r2_hidden(X2,X0) != iProver_top
% 2.52/0.99      | v1_xboole_0(X1) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3637,plain,
% 2.52/0.99      ( r2_hidden(X0,k2_relat_1(sK3)) != iProver_top
% 2.52/0.99      | v1_xboole_0(sK2) != iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_3631,c_936]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_12,plain,
% 2.52/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.52/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_11,plain,
% 2.52/0.99      ( ~ v5_relat_1(X0,X1)
% 2.52/0.99      | m1_subset_1(k1_funct_1(X0,X2),X1)
% 2.52/0.99      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.52/0.99      | ~ v1_funct_1(X0)
% 2.52/0.99      | ~ v1_relat_1(X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_309,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.99      | m1_subset_1(k1_funct_1(X0,X3),X2)
% 2.52/0.99      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.52/0.99      | ~ v1_funct_1(X0)
% 2.52/0.99      | ~ v1_relat_1(X0) ),
% 2.52/0.99      inference(resolution,[status(thm)],[c_12,c_11]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_350,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.99      | m1_subset_1(k1_funct_1(X0,X3),X2)
% 2.52/0.99      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.52/0.99      | ~ v1_relat_1(X0)
% 2.52/0.99      | sK3 != X0 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_309,c_26]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_351,plain,
% 2.52/0.99      ( m1_subset_1(k1_funct_1(sK3,X0),X1)
% 2.52/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.52/0.99      | ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.52/0.99      | ~ v1_relat_1(sK3) ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_350]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_927,plain,
% 2.52/0.99      ( m1_subset_1(k1_funct_1(sK3,X0),X1) = iProver_top
% 2.52/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.52/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.52/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1169,plain,
% 2.52/0.99      ( m1_subset_1(k1_funct_1(sK3,X0),sK2) = iProver_top
% 2.52/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.52/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_929,c_927]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_6,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_937,plain,
% 2.52/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.52/0.99      | r2_hidden(X0,X1) = iProver_top
% 2.52/0.99      | v1_xboole_0(X1) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2293,plain,
% 2.52/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.52/0.99      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top
% 2.52/0.99      | v1_relat_1(sK3) != iProver_top
% 2.52/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_1169,c_937]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_29,plain,
% 2.52/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_8,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1086,plain,
% 2.52/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.52/0.99      | v1_relat_1(X0)
% 2.52/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1213,plain,
% 2.52/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))
% 2.52/0.99      | ~ v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.52/0.99      | v1_relat_1(sK3) ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_1086]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1214,plain,
% 2.52/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) != iProver_top
% 2.52/0.99      | v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != iProver_top
% 2.52/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1213]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_9,plain,
% 2.52/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.52/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1263,plain,
% 2.52/0.99      ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.52/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1264,plain,
% 2.52/0.99      ( v1_relat_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_1263]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3199,plain,
% 2.52/0.99      ( r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top
% 2.52/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.52/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_2293,c_29,c_1214,c_1264]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3200,plain,
% 2.52/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.52/0.99      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top
% 2.52/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.52/0.99      inference(renaming,[status(thm)],[c_3199]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_22,negated_conjecture,
% 2.52/0.99      ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
% 2.52/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_930,plain,
% 2.52/0.99      ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
% 2.52/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3208,plain,
% 2.52/0.99      ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top
% 2.52/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_3200,c_930]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_4044,plain,
% 2.52/0.99      ( r2_hidden(X0,k2_relat_1(sK3)) != iProver_top ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_3637,c_1652,c_3208]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_4052,plain,
% 2.52/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.52/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_928,c_4044]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_4178,plain,
% 2.52/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 2.52/0.99      inference(global_propositional_subsumption,
% 2.52/0.99                [status(thm)],
% 2.52/0.99                [c_4052,c_29,c_1214,c_1264]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_4186,plain,
% 2.52/0.99      ( $false ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_1652,c_4178]) ).
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  ------                               Statistics
% 2.52/0.99  
% 2.52/0.99  ------ General
% 2.52/0.99  
% 2.52/0.99  abstr_ref_over_cycles:                  0
% 2.52/0.99  abstr_ref_under_cycles:                 0
% 2.52/0.99  gc_basic_clause_elim:                   0
% 2.52/0.99  forced_gc_time:                         0
% 2.52/0.99  parsing_time:                           0.01
% 2.52/0.99  unif_index_cands_time:                  0.
% 2.52/0.99  unif_index_add_time:                    0.
% 2.52/0.99  orderings_time:                         0.
% 2.52/0.99  out_proof_time:                         0.007
% 2.52/0.99  total_time:                             0.162
% 2.52/0.99  num_of_symbols:                         51
% 2.52/0.99  num_of_terms:                           5466
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing
% 2.52/0.99  
% 2.52/0.99  num_of_splits:                          0
% 2.52/0.99  num_of_split_atoms:                     0
% 2.52/0.99  num_of_reused_defs:                     0
% 2.52/0.99  num_eq_ax_congr_red:                    27
% 2.52/0.99  num_of_sem_filtered_clauses:            1
% 2.52/1.00  num_of_subtypes:                        0
% 2.52/1.00  monotx_restored_types:                  0
% 2.52/1.00  sat_num_of_epr_types:                   0
% 2.52/1.00  sat_num_of_non_cyclic_types:            0
% 2.52/1.00  sat_guarded_non_collapsed_types:        0
% 2.52/1.00  num_pure_diseq_elim:                    0
% 2.52/1.00  simp_replaced_by:                       0
% 2.52/1.00  res_preprocessed:                       115
% 2.52/1.00  prep_upred:                             0
% 2.52/1.00  prep_unflattend:                        29
% 2.52/1.00  smt_new_axioms:                         0
% 2.52/1.00  pred_elim_cands:                        4
% 2.52/1.00  pred_elim:                              3
% 2.52/1.00  pred_elim_cl:                           6
% 2.52/1.00  pred_elim_cycles:                       6
% 2.52/1.00  merged_defs:                            0
% 2.52/1.00  merged_defs_ncl:                        0
% 2.52/1.00  bin_hyper_res:                          0
% 2.52/1.00  prep_cycles:                            4
% 2.52/1.00  pred_elim_time:                         0.004
% 2.52/1.00  splitting_time:                         0.
% 2.52/1.00  sem_filter_time:                        0.
% 2.52/1.00  monotx_time:                            0.
% 2.52/1.00  subtype_inf_time:                       0.
% 2.52/1.00  
% 2.52/1.00  ------ Problem properties
% 2.52/1.00  
% 2.52/1.00  clauses:                                21
% 2.52/1.00  conjectures:                            3
% 2.52/1.00  epr:                                    2
% 2.52/1.00  horn:                                   17
% 2.52/1.00  ground:                                 6
% 2.52/1.00  unary:                                  7
% 2.52/1.00  binary:                                 3
% 2.52/1.00  lits:                                   49
% 2.52/1.00  lits_eq:                                18
% 2.52/1.00  fd_pure:                                0
% 2.52/1.00  fd_pseudo:                              0
% 2.52/1.00  fd_cond:                                0
% 2.52/1.00  fd_pseudo_cond:                         3
% 2.52/1.00  ac_symbols:                             0
% 2.52/1.00  
% 2.52/1.00  ------ Propositional Solver
% 2.52/1.00  
% 2.52/1.00  prop_solver_calls:                      27
% 2.52/1.00  prop_fast_solver_calls:                 700
% 2.52/1.00  smt_solver_calls:                       0
% 2.52/1.00  smt_fast_solver_calls:                  0
% 2.52/1.00  prop_num_of_clauses:                    1664
% 2.52/1.00  prop_preprocess_simplified:             5490
% 2.52/1.00  prop_fo_subsumed:                       11
% 2.52/1.00  prop_solver_time:                       0.
% 2.52/1.00  smt_solver_time:                        0.
% 2.52/1.00  smt_fast_solver_time:                   0.
% 2.52/1.00  prop_fast_solver_time:                  0.
% 2.52/1.00  prop_unsat_core_time:                   0.
% 2.52/1.00  
% 2.52/1.00  ------ QBF
% 2.52/1.00  
% 2.52/1.00  qbf_q_res:                              0
% 2.52/1.00  qbf_num_tautologies:                    0
% 2.52/1.00  qbf_prep_cycles:                        0
% 2.52/1.00  
% 2.52/1.00  ------ BMC1
% 2.52/1.00  
% 2.52/1.00  bmc1_current_bound:                     -1
% 2.52/1.00  bmc1_last_solved_bound:                 -1
% 2.52/1.00  bmc1_unsat_core_size:                   -1
% 2.52/1.00  bmc1_unsat_core_parents_size:           -1
% 2.52/1.00  bmc1_merge_next_fun:                    0
% 2.52/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.52/1.00  
% 2.52/1.00  ------ Instantiation
% 2.52/1.00  
% 2.52/1.00  inst_num_of_clauses:                    494
% 2.52/1.00  inst_num_in_passive:                    106
% 2.52/1.00  inst_num_in_active:                     202
% 2.52/1.00  inst_num_in_unprocessed:                187
% 2.52/1.00  inst_num_of_loops:                      210
% 2.52/1.00  inst_num_of_learning_restarts:          0
% 2.52/1.00  inst_num_moves_active_passive:          6
% 2.52/1.00  inst_lit_activity:                      0
% 2.52/1.00  inst_lit_activity_moves:                0
% 2.52/1.00  inst_num_tautologies:                   0
% 2.52/1.00  inst_num_prop_implied:                  0
% 2.52/1.00  inst_num_existing_simplified:           0
% 2.52/1.00  inst_num_eq_res_simplified:             0
% 2.52/1.00  inst_num_child_elim:                    0
% 2.52/1.00  inst_num_of_dismatching_blockings:      259
% 2.52/1.00  inst_num_of_non_proper_insts:           484
% 2.52/1.00  inst_num_of_duplicates:                 0
% 2.52/1.00  inst_inst_num_from_inst_to_res:         0
% 2.52/1.00  inst_dismatching_checking_time:         0.
% 2.52/1.00  
% 2.52/1.00  ------ Resolution
% 2.52/1.00  
% 2.52/1.00  res_num_of_clauses:                     0
% 2.52/1.00  res_num_in_passive:                     0
% 2.52/1.00  res_num_in_active:                      0
% 2.52/1.00  res_num_of_loops:                       119
% 2.52/1.00  res_forward_subset_subsumed:            105
% 2.52/1.00  res_backward_subset_subsumed:           2
% 2.52/1.00  res_forward_subsumed:                   0
% 2.52/1.00  res_backward_subsumed:                  0
% 2.52/1.00  res_forward_subsumption_resolution:     0
% 2.52/1.00  res_backward_subsumption_resolution:    0
% 2.52/1.00  res_clause_to_clause_subsumption:       123
% 2.52/1.00  res_orphan_elimination:                 0
% 2.52/1.00  res_tautology_del:                      27
% 2.52/1.00  res_num_eq_res_simplified:              0
% 2.52/1.00  res_num_sel_changes:                    0
% 2.52/1.00  res_moves_from_active_to_pass:          0
% 2.52/1.00  
% 2.52/1.00  ------ Superposition
% 2.52/1.00  
% 2.52/1.00  sup_time_total:                         0.
% 2.52/1.00  sup_time_generating:                    0.
% 2.52/1.00  sup_time_sim_full:                      0.
% 2.52/1.00  sup_time_sim_immed:                     0.
% 2.52/1.00  
% 2.52/1.00  sup_num_of_clauses:                     54
% 2.52/1.00  sup_num_in_active:                      34
% 2.52/1.00  sup_num_in_passive:                     20
% 2.52/1.00  sup_num_of_loops:                       40
% 2.52/1.00  sup_fw_superposition:                   24
% 2.52/1.00  sup_bw_superposition:                   31
% 2.52/1.00  sup_immediate_simplified:               11
% 2.52/1.00  sup_given_eliminated:                   0
% 2.52/1.00  comparisons_done:                       0
% 2.52/1.00  comparisons_avoided:                    13
% 2.52/1.00  
% 2.52/1.00  ------ Simplifications
% 2.52/1.00  
% 2.52/1.00  
% 2.52/1.00  sim_fw_subset_subsumed:                 5
% 2.52/1.00  sim_bw_subset_subsumed:                 2
% 2.52/1.00  sim_fw_subsumed:                        5
% 2.52/1.00  sim_bw_subsumed:                        1
% 2.52/1.00  sim_fw_subsumption_res:                 0
% 2.52/1.00  sim_bw_subsumption_res:                 0
% 2.52/1.00  sim_tautology_del:                      0
% 2.52/1.00  sim_eq_tautology_del:                   2
% 2.52/1.00  sim_eq_res_simp:                        0
% 2.52/1.00  sim_fw_demodulated:                     0
% 2.52/1.00  sim_bw_demodulated:                     5
% 2.52/1.00  sim_light_normalised:                   0
% 2.52/1.00  sim_joinable_taut:                      0
% 2.52/1.00  sim_joinable_simp:                      0
% 2.52/1.00  sim_ac_normalised:                      0
% 2.52/1.00  sim_smt_subsumption:                    0
% 2.52/1.00  
%------------------------------------------------------------------------------
