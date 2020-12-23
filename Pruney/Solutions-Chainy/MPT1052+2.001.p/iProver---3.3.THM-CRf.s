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
% DateTime   : Thu Dec  3 12:08:54 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  201 (1035 expanded)
%              Number of clauses        :  118 ( 354 expanded)
%              Number of leaves         :   28 ( 221 expanded)
%              Depth                    :   17
%              Number of atoms          :  544 (3285 expanded)
%              Number of equality atoms :  290 (1252 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f63,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f23,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f101,f103])).

fof(f20,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f102,f103])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f60,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_relat_1(X2),X1)
          | k1_relat_1(X2) != X0 )
        & r2_hidden(X2,k1_funct_2(X0,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k2_relat_1(sK4),sK3)
        | k1_relat_1(sK4) != sK2 )
      & r2_hidden(sK4,k1_funct_2(sK2,sK3))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK4),sK3)
      | k1_relat_1(sK4) != sK2 )
    & r2_hidden(sK4,k1_funct_2(sK2,sK3))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f48,f60])).

fof(f107,plain,(
    r2_hidden(sK4,k1_funct_2(sK2,sK3)) ),
    inference(cnf_transformation,[],[f61])).

fof(f113,plain,(
    r2_hidden(sK4,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) ),
    inference(definition_unfolding,[],[f107,f103])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f105,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f108,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | k1_relat_1(sK4) != sK2 ),
    inference(cnf_transformation,[],[f61])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f86,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f99,f103])).

fof(f15,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2358,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_39,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_716,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_39,c_36])).

cnf(c_38,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_720,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_716,c_38])).

cnf(c_2325,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_3965,plain,
    ( k1_relset_1(X0,X1,sK0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) = X0
    | k1_xboole_0 = X1
    | v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2358,c_2325])).

cnf(c_43,negated_conjecture,
    ( r2_hidden(sK4,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2328,plain,
    ( r2_hidden(sK4,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2357,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3370,plain,
    ( v1_xboole_0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2328,c_2357])).

cnf(c_9598,plain,
    ( k1_relset_1(sK2,sK3,sK0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3965,c_3370])).

cnf(c_45,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_3966,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2328,c_2325])).

cnf(c_2332,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4984,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2328,c_2332])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2334,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4998,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4984,c_2334])).

cnf(c_5051,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3966,c_4998])).

cnf(c_42,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | k1_relat_1(sK4) != sK2 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2329,plain,
    ( k1_relat_1(sK4) != sK2
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_5276,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5051,c_2329])).

cnf(c_5299,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5276])).

cnf(c_23,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2340,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5275,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5051,c_2340])).

cnf(c_46,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_1514,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2673,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK4),sK3)
    | k2_relat_1(sK4) != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1514])).

cnf(c_2780,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(k2_relat_1(sK4),sK3)
    | k2_relat_1(sK4) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2673])).

cnf(c_2782,plain,
    ( k2_relat_1(sK4) != X0
    | sK3 != sK3
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2780])).

cnf(c_2784,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | sK3 != sK3
    | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2782])).

cnf(c_1510,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2781,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1510])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3120,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3123,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3120])).

cnf(c_25,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2338,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5274,plain,
    ( k2_relat_1(sK4) = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5051,c_2338])).

cnf(c_5937,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5275,c_46,c_2784,c_2781,c_3123,c_5274,c_5276])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2348,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4995,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4984,c_2348])).

cnf(c_16,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2343,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5779,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_2343])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_117,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9755,plain,
    ( v1_relat_1(X2) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5779,c_117])).

cnf(c_9756,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9755])).

cnf(c_9767,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4995,c_9756])).

cnf(c_9791,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4)
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9767])).

cnf(c_9902,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9598,c_45,c_5299,c_5937,c_9791])).

cnf(c_9927,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9902,c_4984])).

cnf(c_15,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2344,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2351,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3280,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2344,c_2351])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2341,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3984,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3280,c_2341])).

cnf(c_2345,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4333,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3984,c_2345])).

cnf(c_9944,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9927,c_4333])).

cnf(c_37,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2333,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5388,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2333,c_3370])).

cnf(c_9921,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9902,c_5388])).

cnf(c_1511,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4833,plain,
    ( X0 != X1
    | X0 = sK2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_9494,plain,
    ( k1_relat_1(sK4) != X0
    | k1_relat_1(sK4) = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_4833])).

cnf(c_9497,plain,
    ( k1_relat_1(sK4) = sK2
    | k1_relat_1(sK4) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9494])).

cnf(c_4730,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_9358,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4730])).

cnf(c_9359,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_9358])).

cnf(c_8028,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_8035,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8028])).

cnf(c_21,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_19,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2342,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5500,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_2342])).

cnf(c_5594,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(k1_relat_1(X0),k1_xboole_0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5500])).

cnf(c_5596,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5594])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4818,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4819,plain,
    ( k1_xboole_0 = sK2
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4818])).

cnf(c_4737,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1510])).

cnf(c_1519,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_4214,plain,
    ( k1_relat_1(sK4) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_4216,plain,
    ( k1_relat_1(sK4) = k1_relat_1(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4214])).

cnf(c_2962,plain,
    ( k1_relat_1(sK4) != X0
    | k1_relat_1(sK4) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1511])).

cnf(c_4213,plain,
    ( k1_relat_1(sK4) != k1_relat_1(X0)
    | k1_relat_1(sK4) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_2962])).

cnf(c_4215,plain,
    ( k1_relat_1(sK4) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK4) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4213])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3189,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3190,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3189])).

cnf(c_3192,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3190])).

cnf(c_3163,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3166,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3163])).

cnf(c_2976,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2977,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2976])).

cnf(c_2973,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_xboole_0
    | k2_relat_1(sK4) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2783,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | k2_relat_1(sK4) != k1_xboole_0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2780])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_147,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_133,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_127,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_121,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9944,c_9921,c_9497,c_9359,c_8035,c_5596,c_4819,c_4737,c_4216,c_4215,c_3192,c_3166,c_3120,c_2977,c_2973,c_2781,c_2783,c_147,c_2,c_133,c_127,c_121,c_42,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.27/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/0.99  
% 3.27/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.27/0.99  
% 3.27/0.99  ------  iProver source info
% 3.27/0.99  
% 3.27/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.27/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.27/0.99  git: non_committed_changes: false
% 3.27/0.99  git: last_make_outside_of_git: false
% 3.27/0.99  
% 3.27/0.99  ------ 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options
% 3.27/0.99  
% 3.27/0.99  --out_options                           all
% 3.27/0.99  --tptp_safe_out                         true
% 3.27/0.99  --problem_path                          ""
% 3.27/0.99  --include_path                          ""
% 3.27/0.99  --clausifier                            res/vclausify_rel
% 3.27/0.99  --clausifier_options                    --mode clausify
% 3.27/0.99  --stdin                                 false
% 3.27/0.99  --stats_out                             all
% 3.27/0.99  
% 3.27/0.99  ------ General Options
% 3.27/0.99  
% 3.27/0.99  --fof                                   false
% 3.27/0.99  --time_out_real                         305.
% 3.27/0.99  --time_out_virtual                      -1.
% 3.27/0.99  --symbol_type_check                     false
% 3.27/0.99  --clausify_out                          false
% 3.27/0.99  --sig_cnt_out                           false
% 3.27/0.99  --trig_cnt_out                          false
% 3.27/0.99  --trig_cnt_out_tolerance                1.
% 3.27/0.99  --trig_cnt_out_sk_spl                   false
% 3.27/0.99  --abstr_cl_out                          false
% 3.27/0.99  
% 3.27/0.99  ------ Global Options
% 3.27/0.99  
% 3.27/0.99  --schedule                              default
% 3.27/0.99  --add_important_lit                     false
% 3.27/0.99  --prop_solver_per_cl                    1000
% 3.27/0.99  --min_unsat_core                        false
% 3.27/0.99  --soft_assumptions                      false
% 3.27/0.99  --soft_lemma_size                       3
% 3.27/0.99  --prop_impl_unit_size                   0
% 3.27/0.99  --prop_impl_unit                        []
% 3.27/0.99  --share_sel_clauses                     true
% 3.27/0.99  --reset_solvers                         false
% 3.27/0.99  --bc_imp_inh                            [conj_cone]
% 3.27/0.99  --conj_cone_tolerance                   3.
% 3.27/0.99  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     num_symb
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       true
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_immed_bw_main                     []
% 3.27/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/0.99  
% 3.27/0.99  ------ Combination Options
% 3.27/0.99  
% 3.27/0.99  --comb_res_mult                         3
% 3.27/0.99  --comb_sup_mult                         2
% 3.27/0.99  --comb_inst_mult                        10
% 3.27/0.99  
% 3.27/0.99  ------ Debug Options
% 3.27/0.99  
% 3.27/0.99  --dbg_backtrace                         false
% 3.27/0.99  --dbg_dump_prop_clauses                 false
% 3.27/0.99  --dbg_dump_prop_clauses_file            -
% 3.27/0.99  --dbg_out_stat                          false
% 3.27/0.99  ------ Parsing...
% 3.27/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.27/0.99  ------ Proving...
% 3.27/0.99  ------ Problem Properties 
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  clauses                                 41
% 3.27/0.99  conjectures                             4
% 3.27/0.99  EPR                                     10
% 3.27/0.99  Horn                                    35
% 3.27/0.99  unary                                   14
% 3.27/0.99  binary                                  13
% 3.27/0.99  lits                                    84
% 3.27/0.99  lits eq                                 29
% 3.27/0.99  fd_pure                                 0
% 3.27/0.99  fd_pseudo                               0
% 3.27/0.99  fd_cond                                 5
% 3.27/0.99  fd_pseudo_cond                          1
% 3.27/0.99  AC symbols                              0
% 3.27/0.99  
% 3.27/0.99  ------ Schedule dynamic 5 is on 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.27/0.99  
% 3.27/0.99  
% 3.27/0.99  ------ 
% 3.27/0.99  Current options:
% 3.27/0.99  ------ 
% 3.27/0.99  
% 3.27/0.99  ------ Input Options
% 3.27/0.99  
% 3.27/0.99  --out_options                           all
% 3.27/0.99  --tptp_safe_out                         true
% 3.27/0.99  --problem_path                          ""
% 3.27/0.99  --include_path                          ""
% 3.27/0.99  --clausifier                            res/vclausify_rel
% 3.27/0.99  --clausifier_options                    --mode clausify
% 3.27/0.99  --stdin                                 false
% 3.27/0.99  --stats_out                             all
% 3.27/0.99  
% 3.27/0.99  ------ General Options
% 3.27/0.99  
% 3.27/0.99  --fof                                   false
% 3.27/0.99  --time_out_real                         305.
% 3.27/0.99  --time_out_virtual                      -1.
% 3.27/0.99  --symbol_type_check                     false
% 3.27/0.99  --clausify_out                          false
% 3.27/0.99  --sig_cnt_out                           false
% 3.27/0.99  --trig_cnt_out                          false
% 3.27/0.99  --trig_cnt_out_tolerance                1.
% 3.27/0.99  --trig_cnt_out_sk_spl                   false
% 3.27/0.99  --abstr_cl_out                          false
% 3.27/0.99  
% 3.27/0.99  ------ Global Options
% 3.27/0.99  
% 3.27/0.99  --schedule                              default
% 3.27/0.99  --add_important_lit                     false
% 3.27/0.99  --prop_solver_per_cl                    1000
% 3.27/0.99  --min_unsat_core                        false
% 3.27/0.99  --soft_assumptions                      false
% 3.27/0.99  --soft_lemma_size                       3
% 3.27/0.99  --prop_impl_unit_size                   0
% 3.27/0.99  --prop_impl_unit                        []
% 3.27/0.99  --share_sel_clauses                     true
% 3.27/0.99  --reset_solvers                         false
% 3.27/0.99  --bc_imp_inh                            [conj_cone]
% 3.27/0.99  --conj_cone_tolerance                   3.
% 3.27/0.99  --extra_neg_conj                        none
% 3.27/0.99  --large_theory_mode                     true
% 3.27/0.99  --prolific_symb_bound                   200
% 3.27/0.99  --lt_threshold                          2000
% 3.27/0.99  --clause_weak_htbl                      true
% 3.27/0.99  --gc_record_bc_elim                     false
% 3.27/0.99  
% 3.27/0.99  ------ Preprocessing Options
% 3.27/0.99  
% 3.27/0.99  --preprocessing_flag                    true
% 3.27/0.99  --time_out_prep_mult                    0.1
% 3.27/0.99  --splitting_mode                        input
% 3.27/0.99  --splitting_grd                         true
% 3.27/0.99  --splitting_cvd                         false
% 3.27/0.99  --splitting_cvd_svl                     false
% 3.27/0.99  --splitting_nvd                         32
% 3.27/0.99  --sub_typing                            true
% 3.27/0.99  --prep_gs_sim                           true
% 3.27/0.99  --prep_unflatten                        true
% 3.27/0.99  --prep_res_sim                          true
% 3.27/0.99  --prep_upred                            true
% 3.27/0.99  --prep_sem_filter                       exhaustive
% 3.27/0.99  --prep_sem_filter_out                   false
% 3.27/0.99  --pred_elim                             true
% 3.27/0.99  --res_sim_input                         true
% 3.27/0.99  --eq_ax_congr_red                       true
% 3.27/0.99  --pure_diseq_elim                       true
% 3.27/0.99  --brand_transform                       false
% 3.27/0.99  --non_eq_to_eq                          false
% 3.27/0.99  --prep_def_merge                        true
% 3.27/0.99  --prep_def_merge_prop_impl              false
% 3.27/0.99  --prep_def_merge_mbd                    true
% 3.27/0.99  --prep_def_merge_tr_red                 false
% 3.27/0.99  --prep_def_merge_tr_cl                  false
% 3.27/0.99  --smt_preprocessing                     true
% 3.27/0.99  --smt_ac_axioms                         fast
% 3.27/0.99  --preprocessed_out                      false
% 3.27/0.99  --preprocessed_stats                    false
% 3.27/0.99  
% 3.27/0.99  ------ Abstraction refinement Options
% 3.27/0.99  
% 3.27/0.99  --abstr_ref                             []
% 3.27/0.99  --abstr_ref_prep                        false
% 3.27/0.99  --abstr_ref_until_sat                   false
% 3.27/0.99  --abstr_ref_sig_restrict                funpre
% 3.27/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.27/0.99  --abstr_ref_under                       []
% 3.27/0.99  
% 3.27/0.99  ------ SAT Options
% 3.27/0.99  
% 3.27/0.99  --sat_mode                              false
% 3.27/0.99  --sat_fm_restart_options                ""
% 3.27/0.99  --sat_gr_def                            false
% 3.27/0.99  --sat_epr_types                         true
% 3.27/0.99  --sat_non_cyclic_types                  false
% 3.27/0.99  --sat_finite_models                     false
% 3.27/0.99  --sat_fm_lemmas                         false
% 3.27/0.99  --sat_fm_prep                           false
% 3.27/0.99  --sat_fm_uc_incr                        true
% 3.27/0.99  --sat_out_model                         small
% 3.27/0.99  --sat_out_clauses                       false
% 3.27/0.99  
% 3.27/0.99  ------ QBF Options
% 3.27/0.99  
% 3.27/0.99  --qbf_mode                              false
% 3.27/0.99  --qbf_elim_univ                         false
% 3.27/0.99  --qbf_dom_inst                          none
% 3.27/0.99  --qbf_dom_pre_inst                      false
% 3.27/0.99  --qbf_sk_in                             false
% 3.27/0.99  --qbf_pred_elim                         true
% 3.27/0.99  --qbf_split                             512
% 3.27/0.99  
% 3.27/0.99  ------ BMC1 Options
% 3.27/0.99  
% 3.27/0.99  --bmc1_incremental                      false
% 3.27/0.99  --bmc1_axioms                           reachable_all
% 3.27/0.99  --bmc1_min_bound                        0
% 3.27/0.99  --bmc1_max_bound                        -1
% 3.27/0.99  --bmc1_max_bound_default                -1
% 3.27/0.99  --bmc1_symbol_reachability              true
% 3.27/0.99  --bmc1_property_lemmas                  false
% 3.27/0.99  --bmc1_k_induction                      false
% 3.27/0.99  --bmc1_non_equiv_states                 false
% 3.27/0.99  --bmc1_deadlock                         false
% 3.27/0.99  --bmc1_ucm                              false
% 3.27/0.99  --bmc1_add_unsat_core                   none
% 3.27/0.99  --bmc1_unsat_core_children              false
% 3.27/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.27/0.99  --bmc1_out_stat                         full
% 3.27/0.99  --bmc1_ground_init                      false
% 3.27/0.99  --bmc1_pre_inst_next_state              false
% 3.27/0.99  --bmc1_pre_inst_state                   false
% 3.27/0.99  --bmc1_pre_inst_reach_state             false
% 3.27/0.99  --bmc1_out_unsat_core                   false
% 3.27/0.99  --bmc1_aig_witness_out                  false
% 3.27/0.99  --bmc1_verbose                          false
% 3.27/0.99  --bmc1_dump_clauses_tptp                false
% 3.27/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.27/0.99  --bmc1_dump_file                        -
% 3.27/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.27/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.27/0.99  --bmc1_ucm_extend_mode                  1
% 3.27/0.99  --bmc1_ucm_init_mode                    2
% 3.27/0.99  --bmc1_ucm_cone_mode                    none
% 3.27/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.27/0.99  --bmc1_ucm_relax_model                  4
% 3.27/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.27/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.27/0.99  --bmc1_ucm_layered_model                none
% 3.27/0.99  --bmc1_ucm_max_lemma_size               10
% 3.27/0.99  
% 3.27/0.99  ------ AIG Options
% 3.27/0.99  
% 3.27/0.99  --aig_mode                              false
% 3.27/0.99  
% 3.27/0.99  ------ Instantiation Options
% 3.27/0.99  
% 3.27/0.99  --instantiation_flag                    true
% 3.27/0.99  --inst_sos_flag                         false
% 3.27/0.99  --inst_sos_phase                        true
% 3.27/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.27/0.99  --inst_lit_sel_side                     none
% 3.27/0.99  --inst_solver_per_active                1400
% 3.27/0.99  --inst_solver_calls_frac                1.
% 3.27/0.99  --inst_passive_queue_type               priority_queues
% 3.27/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.27/0.99  --inst_passive_queues_freq              [25;2]
% 3.27/0.99  --inst_dismatching                      true
% 3.27/0.99  --inst_eager_unprocessed_to_passive     true
% 3.27/0.99  --inst_prop_sim_given                   true
% 3.27/0.99  --inst_prop_sim_new                     false
% 3.27/0.99  --inst_subs_new                         false
% 3.27/0.99  --inst_eq_res_simp                      false
% 3.27/0.99  --inst_subs_given                       false
% 3.27/0.99  --inst_orphan_elimination               true
% 3.27/0.99  --inst_learning_loop_flag               true
% 3.27/0.99  --inst_learning_start                   3000
% 3.27/0.99  --inst_learning_factor                  2
% 3.27/0.99  --inst_start_prop_sim_after_learn       3
% 3.27/0.99  --inst_sel_renew                        solver
% 3.27/0.99  --inst_lit_activity_flag                true
% 3.27/0.99  --inst_restr_to_given                   false
% 3.27/0.99  --inst_activity_threshold               500
% 3.27/0.99  --inst_out_proof                        true
% 3.27/0.99  
% 3.27/0.99  ------ Resolution Options
% 3.27/0.99  
% 3.27/0.99  --resolution_flag                       false
% 3.27/0.99  --res_lit_sel                           adaptive
% 3.27/0.99  --res_lit_sel_side                      none
% 3.27/0.99  --res_ordering                          kbo
% 3.27/0.99  --res_to_prop_solver                    active
% 3.27/0.99  --res_prop_simpl_new                    false
% 3.27/0.99  --res_prop_simpl_given                  true
% 3.27/0.99  --res_passive_queue_type                priority_queues
% 3.27/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.27/0.99  --res_passive_queues_freq               [15;5]
% 3.27/0.99  --res_forward_subs                      full
% 3.27/0.99  --res_backward_subs                     full
% 3.27/0.99  --res_forward_subs_resolution           true
% 3.27/0.99  --res_backward_subs_resolution          true
% 3.27/0.99  --res_orphan_elimination                true
% 3.27/0.99  --res_time_limit                        2.
% 3.27/0.99  --res_out_proof                         true
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Options
% 3.27/0.99  
% 3.27/0.99  --superposition_flag                    true
% 3.27/0.99  --sup_passive_queue_type                priority_queues
% 3.27/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.27/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.27/0.99  --demod_completeness_check              fast
% 3.27/0.99  --demod_use_ground                      true
% 3.27/0.99  --sup_to_prop_solver                    passive
% 3.27/0.99  --sup_prop_simpl_new                    true
% 3.27/0.99  --sup_prop_simpl_given                  true
% 3.27/0.99  --sup_fun_splitting                     false
% 3.27/0.99  --sup_smt_interval                      50000
% 3.27/0.99  
% 3.27/0.99  ------ Superposition Simplification Setup
% 3.27/0.99  
% 3.27/0.99  --sup_indices_passive                   []
% 3.27/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.27/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.27/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/0.99  --sup_full_bw                           [BwDemod]
% 3.27/0.99  --sup_immed_triv                        [TrivRules]
% 3.27/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.27/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.00  --sup_immed_bw_main                     []
% 3.27/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.27/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.27/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.27/1.00  
% 3.27/1.00  ------ Combination Options
% 3.27/1.00  
% 3.27/1.00  --comb_res_mult                         3
% 3.27/1.00  --comb_sup_mult                         2
% 3.27/1.00  --comb_inst_mult                        10
% 3.27/1.00  
% 3.27/1.00  ------ Debug Options
% 3.27/1.00  
% 3.27/1.00  --dbg_backtrace                         false
% 3.27/1.00  --dbg_dump_prop_clauses                 false
% 3.27/1.00  --dbg_dump_prop_clauses_file            -
% 3.27/1.00  --dbg_out_stat                          false
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  ------ Proving...
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  % SZS status Theorem for theBenchmark.p
% 3.27/1.00  
% 3.27/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.27/1.00  
% 3.27/1.00  fof(f1,axiom,(
% 3.27/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f49,plain,(
% 3.27/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.27/1.00    inference(nnf_transformation,[],[f1])).
% 3.27/1.00  
% 3.27/1.00  fof(f50,plain,(
% 3.27/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.27/1.00    inference(rectify,[],[f49])).
% 3.27/1.00  
% 3.27/1.00  fof(f51,plain,(
% 3.27/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.27/1.00    introduced(choice_axiom,[])).
% 3.27/1.00  
% 3.27/1.00  fof(f52,plain,(
% 3.27/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.27/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 3.27/1.00  
% 3.27/1.00  fof(f63,plain,(
% 3.27/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f52])).
% 3.27/1.00  
% 3.27/1.00  fof(f22,axiom,(
% 3.27/1.00    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f44,plain,(
% 3.27/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 3.27/1.00    inference(ennf_transformation,[],[f22])).
% 3.27/1.00  
% 3.27/1.00  fof(f101,plain,(
% 3.27/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 3.27/1.00    inference(cnf_transformation,[],[f44])).
% 3.27/1.00  
% 3.27/1.00  fof(f23,axiom,(
% 3.27/1.00    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f103,plain,(
% 3.27/1.00    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 3.27/1.00    inference(cnf_transformation,[],[f23])).
% 3.27/1.00  
% 3.27/1.00  fof(f111,plain,(
% 3.27/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 3.27/1.00    inference(definition_unfolding,[],[f101,f103])).
% 3.27/1.00  
% 3.27/1.00  fof(f20,axiom,(
% 3.27/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f40,plain,(
% 3.27/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/1.00    inference(ennf_transformation,[],[f20])).
% 3.27/1.00  
% 3.27/1.00  fof(f41,plain,(
% 3.27/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/1.00    inference(flattening,[],[f40])).
% 3.27/1.00  
% 3.27/1.00  fof(f59,plain,(
% 3.27/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/1.00    inference(nnf_transformation,[],[f41])).
% 3.27/1.00  
% 3.27/1.00  fof(f93,plain,(
% 3.27/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/1.00    inference(cnf_transformation,[],[f59])).
% 3.27/1.00  
% 3.27/1.00  fof(f102,plain,(
% 3.27/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 3.27/1.00    inference(cnf_transformation,[],[f44])).
% 3.27/1.00  
% 3.27/1.00  fof(f110,plain,(
% 3.27/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 3.27/1.00    inference(definition_unfolding,[],[f102,f103])).
% 3.27/1.00  
% 3.27/1.00  fof(f25,conjecture,(
% 3.27/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f26,negated_conjecture,(
% 3.27/1.00    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 3.27/1.00    inference(negated_conjecture,[],[f25])).
% 3.27/1.00  
% 3.27/1.00  fof(f47,plain,(
% 3.27/1.00    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.27/1.00    inference(ennf_transformation,[],[f26])).
% 3.27/1.00  
% 3.27/1.00  fof(f48,plain,(
% 3.27/1.00    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.27/1.00    inference(flattening,[],[f47])).
% 3.27/1.00  
% 3.27/1.00  fof(f60,plain,(
% 3.27/1.00    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => ((~r1_tarski(k2_relat_1(sK4),sK3) | k1_relat_1(sK4) != sK2) & r2_hidden(sK4,k1_funct_2(sK2,sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 3.27/1.00    introduced(choice_axiom,[])).
% 3.27/1.00  
% 3.27/1.00  fof(f61,plain,(
% 3.27/1.00    (~r1_tarski(k2_relat_1(sK4),sK3) | k1_relat_1(sK4) != sK2) & r2_hidden(sK4,k1_funct_2(sK2,sK3)) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 3.27/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f48,f60])).
% 3.27/1.00  
% 3.27/1.00  fof(f107,plain,(
% 3.27/1.00    r2_hidden(sK4,k1_funct_2(sK2,sK3))),
% 3.27/1.00    inference(cnf_transformation,[],[f61])).
% 3.27/1.00  
% 3.27/1.00  fof(f113,plain,(
% 3.27/1.00    r2_hidden(sK4,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))),
% 3.27/1.00    inference(definition_unfolding,[],[f107,f103])).
% 3.27/1.00  
% 3.27/1.00  fof(f62,plain,(
% 3.27/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f52])).
% 3.27/1.00  
% 3.27/1.00  fof(f105,plain,(
% 3.27/1.00    v1_relat_1(sK4)),
% 3.27/1.00    inference(cnf_transformation,[],[f61])).
% 3.27/1.00  
% 3.27/1.00  fof(f19,axiom,(
% 3.27/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f39,plain,(
% 3.27/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.27/1.00    inference(ennf_transformation,[],[f19])).
% 3.27/1.00  
% 3.27/1.00  fof(f92,plain,(
% 3.27/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.27/1.00    inference(cnf_transformation,[],[f39])).
% 3.27/1.00  
% 3.27/1.00  fof(f108,plain,(
% 3.27/1.00    ~r1_tarski(k2_relat_1(sK4),sK3) | k1_relat_1(sK4) != sK2),
% 3.27/1.00    inference(cnf_transformation,[],[f61])).
% 3.27/1.00  
% 3.27/1.00  fof(f16,axiom,(
% 3.27/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f35,plain,(
% 3.27/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.27/1.00    inference(ennf_transformation,[],[f16])).
% 3.27/1.00  
% 3.27/1.00  fof(f36,plain,(
% 3.27/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.27/1.00    inference(flattening,[],[f35])).
% 3.27/1.00  
% 3.27/1.00  fof(f84,plain,(
% 3.27/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f36])).
% 3.27/1.00  
% 3.27/1.00  fof(f5,axiom,(
% 3.27/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f69,plain,(
% 3.27/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f5])).
% 3.27/1.00  
% 3.27/1.00  fof(f17,axiom,(
% 3.27/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f37,plain,(
% 3.27/1.00    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.27/1.00    inference(ennf_transformation,[],[f17])).
% 3.27/1.00  
% 3.27/1.00  fof(f56,plain,(
% 3.27/1.00    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.27/1.00    inference(nnf_transformation,[],[f37])).
% 3.27/1.00  
% 3.27/1.00  fof(f86,plain,(
% 3.27/1.00    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f56])).
% 3.27/1.00  
% 3.27/1.00  fof(f8,axiom,(
% 3.27/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f55,plain,(
% 3.27/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.27/1.00    inference(nnf_transformation,[],[f8])).
% 3.27/1.00  
% 3.27/1.00  fof(f72,plain,(
% 3.27/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.27/1.00    inference(cnf_transformation,[],[f55])).
% 3.27/1.00  
% 3.27/1.00  fof(f13,axiom,(
% 3.27/1.00    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f32,plain,(
% 3.27/1.00    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.27/1.00    inference(ennf_transformation,[],[f13])).
% 3.27/1.00  
% 3.27/1.00  fof(f79,plain,(
% 3.27/1.00    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.27/1.00    inference(cnf_transformation,[],[f32])).
% 3.27/1.00  
% 3.27/1.00  fof(f14,axiom,(
% 3.27/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f33,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.27/1.00    inference(ennf_transformation,[],[f14])).
% 3.27/1.00  
% 3.27/1.00  fof(f34,plain,(
% 3.27/1.00    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.27/1.00    inference(flattening,[],[f33])).
% 3.27/1.00  
% 3.27/1.00  fof(f81,plain,(
% 3.27/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f34])).
% 3.27/1.00  
% 3.27/1.00  fof(f11,axiom,(
% 3.27/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f76,plain,(
% 3.27/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.27/1.00    inference(cnf_transformation,[],[f11])).
% 3.27/1.00  
% 3.27/1.00  fof(f12,axiom,(
% 3.27/1.00    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f77,plain,(
% 3.27/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f12])).
% 3.27/1.00  
% 3.27/1.00  fof(f6,axiom,(
% 3.27/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f28,plain,(
% 3.27/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.27/1.00    inference(ennf_transformation,[],[f6])).
% 3.27/1.00  
% 3.27/1.00  fof(f70,plain,(
% 3.27/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f28])).
% 3.27/1.00  
% 3.27/1.00  fof(f85,plain,(
% 3.27/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f36])).
% 3.27/1.00  
% 3.27/1.00  fof(f21,axiom,(
% 3.27/1.00    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f42,plain,(
% 3.27/1.00    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.27/1.00    inference(ennf_transformation,[],[f21])).
% 3.27/1.00  
% 3.27/1.00  fof(f43,plain,(
% 3.27/1.00    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.27/1.00    inference(flattening,[],[f42])).
% 3.27/1.00  
% 3.27/1.00  fof(f99,plain,(
% 3.27/1.00    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f43])).
% 3.27/1.00  
% 3.27/1.00  fof(f109,plain,(
% 3.27/1.00    ( ! [X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.27/1.00    inference(definition_unfolding,[],[f99,f103])).
% 3.27/1.00  
% 3.27/1.00  fof(f15,axiom,(
% 3.27/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f82,plain,(
% 3.27/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.27/1.00    inference(cnf_transformation,[],[f15])).
% 3.27/1.00  
% 3.27/1.00  fof(f80,plain,(
% 3.27/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f34])).
% 3.27/1.00  
% 3.27/1.00  fof(f3,axiom,(
% 3.27/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f27,plain,(
% 3.27/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.27/1.00    inference(ennf_transformation,[],[f3])).
% 3.27/1.00  
% 3.27/1.00  fof(f65,plain,(
% 3.27/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f27])).
% 3.27/1.00  
% 3.27/1.00  fof(f4,axiom,(
% 3.27/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f53,plain,(
% 3.27/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.27/1.00    inference(nnf_transformation,[],[f4])).
% 3.27/1.00  
% 3.27/1.00  fof(f54,plain,(
% 3.27/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.27/1.00    inference(flattening,[],[f53])).
% 3.27/1.00  
% 3.27/1.00  fof(f68,plain,(
% 3.27/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f54])).
% 3.27/1.00  
% 3.27/1.00  fof(f2,axiom,(
% 3.27/1.00    v1_xboole_0(k1_xboole_0)),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f64,plain,(
% 3.27/1.00    v1_xboole_0(k1_xboole_0)),
% 3.27/1.00    inference(cnf_transformation,[],[f2])).
% 3.27/1.00  
% 3.27/1.00  fof(f7,axiom,(
% 3.27/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f71,plain,(
% 3.27/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.27/1.00    inference(cnf_transformation,[],[f7])).
% 3.27/1.00  
% 3.27/1.00  fof(f10,axiom,(
% 3.27/1.00    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.27/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.27/1.00  
% 3.27/1.00  fof(f31,plain,(
% 3.27/1.00    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.27/1.00    inference(ennf_transformation,[],[f10])).
% 3.27/1.00  
% 3.27/1.00  fof(f75,plain,(
% 3.27/1.00    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.27/1.00    inference(cnf_transformation,[],[f31])).
% 3.27/1.00  
% 3.27/1.00  cnf(c_0,plain,
% 3.27/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2358,plain,
% 3.27/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.27/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_39,plain,
% 3.27/1.00      ( v1_funct_2(X0,X1,X2)
% 3.27/1.00      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
% 3.27/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_36,plain,
% 3.27/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.27/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.27/1.00      | k1_xboole_0 = X2 ),
% 3.27/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_716,plain,
% 3.27/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/1.00      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 3.27/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.27/1.00      | k1_xboole_0 = X2 ),
% 3.27/1.00      inference(resolution,[status(thm)],[c_39,c_36]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_38,plain,
% 3.27/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/1.00      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
% 3.27/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_720,plain,
% 3.27/1.00      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 3.27/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.27/1.00      | k1_xboole_0 = X2 ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_716,c_38]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2325,plain,
% 3.27/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.27/1.00      | k1_xboole_0 = X1
% 3.27/1.00      | r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3965,plain,
% 3.27/1.00      ( k1_relset_1(X0,X1,sK0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) = X0
% 3.27/1.00      | k1_xboole_0 = X1
% 3.27/1.00      | v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) = iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_2358,c_2325]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_43,negated_conjecture,
% 3.27/1.00      ( r2_hidden(sK4,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) ),
% 3.27/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2328,plain,
% 3.27/1.00      ( r2_hidden(sK4,k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_1,plain,
% 3.27/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.27/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2357,plain,
% 3.27/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.27/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3370,plain,
% 3.27/1.00      ( v1_xboole_0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3))) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_2328,c_2357]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9598,plain,
% 3.27/1.00      ( k1_relset_1(sK2,sK3,sK0(k5_partfun1(sK2,sK3,k3_partfun1(k1_xboole_0,sK2,sK3)))) = sK2
% 3.27/1.00      | sK3 = k1_xboole_0 ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_3965,c_3370]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_45,negated_conjecture,
% 3.27/1.00      ( v1_relat_1(sK4) ),
% 3.27/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3966,plain,
% 3.27/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_2328,c_2325]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2332,plain,
% 3.27/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.27/1.00      | r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4984,plain,
% 3.27/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_2328,c_2332]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_30,plain,
% 3.27/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.27/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2334,plain,
% 3.27/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.27/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4998,plain,
% 3.27/1.00      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_4984,c_2334]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5051,plain,
% 3.27/1.00      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_3966,c_4998]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_42,negated_conjecture,
% 3.27/1.00      ( ~ r1_tarski(k2_relat_1(sK4),sK3) | k1_relat_1(sK4) != sK2 ),
% 3.27/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2329,plain,
% 3.27/1.00      ( k1_relat_1(sK4) != sK2
% 3.27/1.00      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5276,plain,
% 3.27/1.00      ( sK3 = k1_xboole_0
% 3.27/1.00      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_5051,c_2329]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5299,plain,
% 3.27/1.00      ( ~ r1_tarski(k2_relat_1(sK4),sK3) | sK3 = k1_xboole_0 ),
% 3.27/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5276]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_23,plain,
% 3.27/1.00      ( ~ v1_relat_1(X0)
% 3.27/1.00      | k1_relat_1(X0) != k1_xboole_0
% 3.27/1.00      | k1_xboole_0 = X0 ),
% 3.27/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2340,plain,
% 3.27/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.27/1.00      | k1_xboole_0 = X0
% 3.27/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5275,plain,
% 3.27/1.00      ( sK2 != k1_xboole_0
% 3.27/1.00      | sK3 = k1_xboole_0
% 3.27/1.00      | sK4 = k1_xboole_0
% 3.27/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_5051,c_2340]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_46,plain,
% 3.27/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_1514,plain,
% 3.27/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.27/1.00      theory(equality) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2673,plain,
% 3.27/1.00      ( ~ r1_tarski(X0,X1)
% 3.27/1.00      | r1_tarski(k2_relat_1(sK4),sK3)
% 3.27/1.00      | k2_relat_1(sK4) != X0
% 3.27/1.00      | sK3 != X1 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_1514]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2780,plain,
% 3.27/1.00      ( ~ r1_tarski(X0,sK3)
% 3.27/1.00      | r1_tarski(k2_relat_1(sK4),sK3)
% 3.27/1.00      | k2_relat_1(sK4) != X0
% 3.27/1.00      | sK3 != sK3 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_2673]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2782,plain,
% 3.27/1.00      ( k2_relat_1(sK4) != X0
% 3.27/1.00      | sK3 != sK3
% 3.27/1.00      | r1_tarski(X0,sK3) != iProver_top
% 3.27/1.00      | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_2780]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2784,plain,
% 3.27/1.00      ( k2_relat_1(sK4) != k1_xboole_0
% 3.27/1.00      | sK3 != sK3
% 3.27/1.00      | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
% 3.27/1.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_2782]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_1510,plain,( X0 = X0 ),theory(equality) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2781,plain,
% 3.27/1.00      ( sK3 = sK3 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_1510]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_7,plain,
% 3.27/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3120,plain,
% 3.27/1.00      ( r1_tarski(k1_xboole_0,sK3) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3123,plain,
% 3.27/1.00      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_3120]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_25,plain,
% 3.27/1.00      ( ~ v1_relat_1(X0)
% 3.27/1.00      | k1_relat_1(X0) != k1_xboole_0
% 3.27/1.00      | k2_relat_1(X0) = k1_xboole_0 ),
% 3.27/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2338,plain,
% 3.27/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.27/1.00      | k2_relat_1(X0) = k1_xboole_0
% 3.27/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5274,plain,
% 3.27/1.00      ( k2_relat_1(sK4) = k1_xboole_0
% 3.27/1.00      | sK2 != k1_xboole_0
% 3.27/1.00      | sK3 = k1_xboole_0
% 3.27/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_5051,c_2338]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5937,plain,
% 3.27/1.00      ( sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_5275,c_46,c_2784,c_2781,c_3123,c_5274,c_5276]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_11,plain,
% 3.27/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.27/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2348,plain,
% 3.27/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.27/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4995,plain,
% 3.27/1.00      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_4984,c_2348]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_16,plain,
% 3.27/1.00      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 3.27/1.00      | k1_xboole_0 = X0
% 3.27/1.00      | k1_xboole_0 = X1 ),
% 3.27/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_18,plain,
% 3.27/1.00      ( ~ r1_tarski(X0,X1)
% 3.27/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.27/1.00      | ~ v1_relat_1(X1)
% 3.27/1.00      | ~ v1_relat_1(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2343,plain,
% 3.27/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.27/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 3.27/1.00      | v1_relat_1(X0) != iProver_top
% 3.27/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5779,plain,
% 3.27/1.00      ( k1_xboole_0 = X0
% 3.27/1.00      | k1_xboole_0 = X1
% 3.27/1.00      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 3.27/1.00      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 3.27/1.00      | v1_relat_1(X2) != iProver_top
% 3.27/1.00      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_16,c_2343]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_14,plain,
% 3.27/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.27/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_117,plain,
% 3.27/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9755,plain,
% 3.27/1.00      ( v1_relat_1(X2) != iProver_top
% 3.27/1.00      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 3.27/1.00      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 3.27/1.00      | k1_xboole_0 = X1
% 3.27/1.00      | k1_xboole_0 = X0 ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_5779,c_117]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9756,plain,
% 3.27/1.00      ( k1_xboole_0 = X0
% 3.27/1.00      | k1_xboole_0 = X1
% 3.27/1.00      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 3.27/1.00      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 3.27/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.27/1.00      inference(renaming,[status(thm)],[c_9755]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9767,plain,
% 3.27/1.00      ( sK2 = k1_xboole_0
% 3.27/1.00      | sK3 = k1_xboole_0
% 3.27/1.00      | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
% 3.27/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_4995,c_9756]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9791,plain,
% 3.27/1.00      ( r1_tarski(k2_relat_1(sK4),sK3)
% 3.27/1.00      | ~ v1_relat_1(sK4)
% 3.27/1.00      | sK2 = k1_xboole_0
% 3.27/1.00      | sK3 = k1_xboole_0 ),
% 3.27/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_9767]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9902,plain,
% 3.27/1.00      ( sK3 = k1_xboole_0 ),
% 3.27/1.00      inference(global_propositional_subsumption,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_9598,c_45,c_5299,c_5937,c_9791]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9927,plain,
% 3.27/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) = iProver_top ),
% 3.27/1.00      inference(demodulation,[status(thm)],[c_9902,c_4984]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_15,plain,
% 3.27/1.00      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
% 3.27/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2344,plain,
% 3.27/1.00      ( r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_8,plain,
% 3.27/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.27/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2351,plain,
% 3.27/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3280,plain,
% 3.27/1.00      ( k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_2344,c_2351]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_22,plain,
% 3.27/1.00      ( ~ v1_relat_1(X0)
% 3.27/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.27/1.00      | k1_xboole_0 = X0 ),
% 3.27/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2341,plain,
% 3.27/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 3.27/1.00      | k1_xboole_0 = X0
% 3.27/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3984,plain,
% 3.27/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
% 3.27/1.00      | v1_relat_1(k2_zfmisc_1(X0,k1_xboole_0)) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_3280,c_2341]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2345,plain,
% 3.27/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4333,plain,
% 3.27/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.27/1.00      inference(forward_subsumption_resolution,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_3984,c_2345]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9944,plain,
% 3.27/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.27/1.00      inference(demodulation,[status(thm)],[c_9927,c_4333]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_37,plain,
% 3.27/1.00      ( ~ v1_xboole_0(X0)
% 3.27/1.00      | v1_xboole_0(X1)
% 3.27/1.00      | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ),
% 3.27/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2333,plain,
% 3.27/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.27/1.00      | v1_xboole_0(X1) = iProver_top
% 3.27/1.00      | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5388,plain,
% 3.27/1.00      ( v1_xboole_0(sK2) = iProver_top
% 3.27/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_2333,c_3370]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9921,plain,
% 3.27/1.00      ( v1_xboole_0(sK2) = iProver_top
% 3.27/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.27/1.00      inference(demodulation,[status(thm)],[c_9902,c_5388]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_1511,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4833,plain,
% 3.27/1.00      ( X0 != X1 | X0 = sK2 | sK2 != X1 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_1511]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9494,plain,
% 3.27/1.00      ( k1_relat_1(sK4) != X0 | k1_relat_1(sK4) = sK2 | sK2 != X0 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_4833]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9497,plain,
% 3.27/1.00      ( k1_relat_1(sK4) = sK2
% 3.27/1.00      | k1_relat_1(sK4) != k1_xboole_0
% 3.27/1.00      | sK2 != k1_xboole_0 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_9494]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4730,plain,
% 3.27/1.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_1511]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9358,plain,
% 3.27/1.00      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_4730]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9359,plain,
% 3.27/1.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_9358]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_8028,plain,
% 3.27/1.00      ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
% 3.27/1.00      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_8035,plain,
% 3.27/1.00      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
% 3.27/1.00      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_8028]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_21,plain,
% 3.27/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.27/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_19,plain,
% 3.27/1.00      ( ~ r1_tarski(X0,X1)
% 3.27/1.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 3.27/1.00      | ~ v1_relat_1(X1)
% 3.27/1.00      | ~ v1_relat_1(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2342,plain,
% 3.27/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.27/1.00      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 3.27/1.00      | v1_relat_1(X0) != iProver_top
% 3.27/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5500,plain,
% 3.27/1.00      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.27/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top
% 3.27/1.00      | v1_relat_1(X0) != iProver_top
% 3.27/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.27/1.00      inference(superposition,[status(thm)],[c_21,c_2342]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5594,plain,
% 3.27/1.00      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.27/1.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0)
% 3.27/1.00      | ~ v1_relat_1(X0)
% 3.27/1.00      | ~ v1_relat_1(k1_xboole_0) ),
% 3.27/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_5500]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_5596,plain,
% 3.27/1.00      ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
% 3.27/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.27/1.00      | ~ v1_relat_1(k1_xboole_0) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_5594]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3,plain,
% 3.27/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.27/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4818,plain,
% 3.27/1.00      ( ~ v1_xboole_0(sK2) | k1_xboole_0 = sK2 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4819,plain,
% 3.27/1.00      ( k1_xboole_0 = sK2 | v1_xboole_0(sK2) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_4818]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4737,plain,
% 3.27/1.00      ( sK2 = sK2 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_1510]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_1519,plain,
% 3.27/1.00      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 3.27/1.00      theory(equality) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4214,plain,
% 3.27/1.00      ( k1_relat_1(sK4) = k1_relat_1(X0) | sK4 != X0 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_1519]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4216,plain,
% 3.27/1.00      ( k1_relat_1(sK4) = k1_relat_1(k1_xboole_0) | sK4 != k1_xboole_0 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_4214]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2962,plain,
% 3.27/1.00      ( k1_relat_1(sK4) != X0
% 3.27/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 3.27/1.00      | k1_xboole_0 != X0 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_1511]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4213,plain,
% 3.27/1.00      ( k1_relat_1(sK4) != k1_relat_1(X0)
% 3.27/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 3.27/1.00      | k1_xboole_0 != k1_relat_1(X0) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_2962]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4215,plain,
% 3.27/1.00      ( k1_relat_1(sK4) != k1_relat_1(k1_xboole_0)
% 3.27/1.00      | k1_relat_1(sK4) = k1_xboole_0
% 3.27/1.00      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_4213]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_4,plain,
% 3.27/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.27/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3189,plain,
% 3.27/1.00      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3190,plain,
% 3.27/1.00      ( sK4 = X0
% 3.27/1.00      | r1_tarski(X0,sK4) != iProver_top
% 3.27/1.00      | r1_tarski(sK4,X0) != iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_3189]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3192,plain,
% 3.27/1.00      ( sK4 = k1_xboole_0
% 3.27/1.00      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 3.27/1.00      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_3190]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3163,plain,
% 3.27/1.00      ( r1_tarski(k1_xboole_0,sK4) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_3166,plain,
% 3.27/1.00      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_3163]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2976,plain,
% 3.27/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))
% 3.27/1.00      | r1_tarski(sK4,k1_xboole_0) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2977,plain,
% 3.27/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.27/1.00      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_2976]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2973,plain,
% 3.27/1.00      ( ~ v1_relat_1(sK4)
% 3.27/1.00      | k1_relat_1(sK4) != k1_xboole_0
% 3.27/1.00      | k2_relat_1(sK4) = k1_xboole_0 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2783,plain,
% 3.27/1.00      ( r1_tarski(k2_relat_1(sK4),sK3)
% 3.27/1.00      | ~ r1_tarski(k1_xboole_0,sK3)
% 3.27/1.00      | k2_relat_1(sK4) != k1_xboole_0
% 3.27/1.00      | sK3 != sK3 ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_2780]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_2,plain,
% 3.27/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_147,plain,
% 3.27/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.27/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_9,plain,
% 3.27/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.27/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_133,plain,
% 3.27/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_127,plain,
% 3.27/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 3.27/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_13,plain,
% 3.27/1.00      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.27/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(c_121,plain,
% 3.27/1.00      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 3.27/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.27/1.00  
% 3.27/1.00  cnf(contradiction,plain,
% 3.27/1.00      ( $false ),
% 3.27/1.00      inference(minisat,
% 3.27/1.00                [status(thm)],
% 3.27/1.00                [c_9944,c_9921,c_9497,c_9359,c_8035,c_5596,c_4819,c_4737,
% 3.27/1.00                 c_4216,c_4215,c_3192,c_3166,c_3120,c_2977,c_2973,c_2781,
% 3.27/1.00                 c_2783,c_147,c_2,c_133,c_127,c_121,c_42,c_45]) ).
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.27/1.00  
% 3.27/1.00  ------                               Statistics
% 3.27/1.00  
% 3.27/1.00  ------ General
% 3.27/1.00  
% 3.27/1.00  abstr_ref_over_cycles:                  0
% 3.27/1.00  abstr_ref_under_cycles:                 0
% 3.27/1.00  gc_basic_clause_elim:                   0
% 3.27/1.00  forced_gc_time:                         0
% 3.27/1.00  parsing_time:                           0.012
% 3.27/1.00  unif_index_cands_time:                  0.
% 3.27/1.00  unif_index_add_time:                    0.
% 3.27/1.00  orderings_time:                         0.
% 3.27/1.00  out_proof_time:                         0.012
% 3.27/1.00  total_time:                             0.257
% 3.27/1.00  num_of_symbols:                         52
% 3.27/1.00  num_of_terms:                           6654
% 3.27/1.00  
% 3.27/1.00  ------ Preprocessing
% 3.27/1.00  
% 3.27/1.00  num_of_splits:                          0
% 3.27/1.00  num_of_split_atoms:                     0
% 3.27/1.00  num_of_reused_defs:                     0
% 3.27/1.00  num_eq_ax_congr_red:                    19
% 3.27/1.00  num_of_sem_filtered_clauses:            1
% 3.27/1.00  num_of_subtypes:                        0
% 3.27/1.00  monotx_restored_types:                  0
% 3.27/1.00  sat_num_of_epr_types:                   0
% 3.27/1.00  sat_num_of_non_cyclic_types:            0
% 3.27/1.00  sat_guarded_non_collapsed_types:        0
% 3.27/1.00  num_pure_diseq_elim:                    0
% 3.27/1.00  simp_replaced_by:                       0
% 3.27/1.00  res_preprocessed:                       199
% 3.27/1.00  prep_upred:                             0
% 3.27/1.00  prep_unflattend:                        105
% 3.27/1.00  smt_new_axioms:                         0
% 3.27/1.00  pred_elim_cands:                        6
% 3.27/1.00  pred_elim:                              1
% 3.27/1.00  pred_elim_cl:                           4
% 3.27/1.00  pred_elim_cycles:                       6
% 3.27/1.00  merged_defs:                            8
% 3.27/1.00  merged_defs_ncl:                        0
% 3.27/1.00  bin_hyper_res:                          8
% 3.27/1.00  prep_cycles:                            4
% 3.27/1.00  pred_elim_time:                         0.013
% 3.27/1.00  splitting_time:                         0.
% 3.27/1.00  sem_filter_time:                        0.
% 3.27/1.00  monotx_time:                            0.001
% 3.27/1.00  subtype_inf_time:                       0.
% 3.27/1.00  
% 3.27/1.00  ------ Problem properties
% 3.27/1.00  
% 3.27/1.00  clauses:                                41
% 3.27/1.00  conjectures:                            4
% 3.27/1.00  epr:                                    10
% 3.27/1.00  horn:                                   35
% 3.27/1.00  ground:                                 7
% 3.27/1.00  unary:                                  14
% 3.27/1.00  binary:                                 13
% 3.27/1.00  lits:                                   84
% 3.27/1.00  lits_eq:                                29
% 3.27/1.00  fd_pure:                                0
% 3.27/1.00  fd_pseudo:                              0
% 3.27/1.00  fd_cond:                                5
% 3.27/1.00  fd_pseudo_cond:                         1
% 3.27/1.00  ac_symbols:                             0
% 3.27/1.00  
% 3.27/1.00  ------ Propositional Solver
% 3.27/1.00  
% 3.27/1.00  prop_solver_calls:                      28
% 3.27/1.00  prop_fast_solver_calls:                 1478
% 3.27/1.00  smt_solver_calls:                       0
% 3.27/1.00  smt_fast_solver_calls:                  0
% 3.27/1.00  prop_num_of_clauses:                    3204
% 3.27/1.00  prop_preprocess_simplified:             9329
% 3.27/1.00  prop_fo_subsumed:                       45
% 3.27/1.00  prop_solver_time:                       0.
% 3.27/1.00  smt_solver_time:                        0.
% 3.27/1.00  smt_fast_solver_time:                   0.
% 3.27/1.00  prop_fast_solver_time:                  0.
% 3.27/1.00  prop_unsat_core_time:                   0.
% 3.27/1.00  
% 3.27/1.00  ------ QBF
% 3.27/1.00  
% 3.27/1.00  qbf_q_res:                              0
% 3.27/1.00  qbf_num_tautologies:                    0
% 3.27/1.00  qbf_prep_cycles:                        0
% 3.27/1.00  
% 3.27/1.00  ------ BMC1
% 3.27/1.00  
% 3.27/1.00  bmc1_current_bound:                     -1
% 3.27/1.00  bmc1_last_solved_bound:                 -1
% 3.27/1.00  bmc1_unsat_core_size:                   -1
% 3.27/1.00  bmc1_unsat_core_parents_size:           -1
% 3.27/1.00  bmc1_merge_next_fun:                    0
% 3.27/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.27/1.00  
% 3.27/1.00  ------ Instantiation
% 3.27/1.00  
% 3.27/1.00  inst_num_of_clauses:                    1041
% 3.27/1.00  inst_num_in_passive:                    41
% 3.27/1.00  inst_num_in_active:                     481
% 3.27/1.00  inst_num_in_unprocessed:                519
% 3.27/1.00  inst_num_of_loops:                      560
% 3.27/1.00  inst_num_of_learning_restarts:          0
% 3.27/1.00  inst_num_moves_active_passive:          76
% 3.27/1.00  inst_lit_activity:                      0
% 3.27/1.00  inst_lit_activity_moves:                0
% 3.27/1.00  inst_num_tautologies:                   0
% 3.27/1.00  inst_num_prop_implied:                  0
% 3.27/1.00  inst_num_existing_simplified:           0
% 3.27/1.00  inst_num_eq_res_simplified:             0
% 3.27/1.00  inst_num_child_elim:                    0
% 3.27/1.00  inst_num_of_dismatching_blockings:      193
% 3.27/1.00  inst_num_of_non_proper_insts:           927
% 3.27/1.00  inst_num_of_duplicates:                 0
% 3.27/1.00  inst_inst_num_from_inst_to_res:         0
% 3.27/1.00  inst_dismatching_checking_time:         0.
% 3.27/1.00  
% 3.27/1.00  ------ Resolution
% 3.27/1.00  
% 3.27/1.00  res_num_of_clauses:                     0
% 3.27/1.00  res_num_in_passive:                     0
% 3.27/1.00  res_num_in_active:                      0
% 3.27/1.00  res_num_of_loops:                       203
% 3.27/1.00  res_forward_subset_subsumed:            72
% 3.27/1.00  res_backward_subset_subsumed:           0
% 3.27/1.00  res_forward_subsumed:                   0
% 3.27/1.00  res_backward_subsumed:                  0
% 3.27/1.00  res_forward_subsumption_resolution:     2
% 3.27/1.00  res_backward_subsumption_resolution:    0
% 3.27/1.00  res_clause_to_clause_subsumption:       646
% 3.27/1.00  res_orphan_elimination:                 0
% 3.27/1.00  res_tautology_del:                      58
% 3.27/1.00  res_num_eq_res_simplified:              0
% 3.27/1.00  res_num_sel_changes:                    0
% 3.27/1.00  res_moves_from_active_to_pass:          0
% 3.27/1.00  
% 3.27/1.00  ------ Superposition
% 3.27/1.00  
% 3.27/1.00  sup_time_total:                         0.
% 3.27/1.00  sup_time_generating:                    0.
% 3.27/1.00  sup_time_sim_full:                      0.
% 3.27/1.00  sup_time_sim_immed:                     0.
% 3.27/1.00  
% 3.27/1.00  sup_num_of_clauses:                     110
% 3.27/1.00  sup_num_in_active:                      63
% 3.27/1.00  sup_num_in_passive:                     47
% 3.27/1.00  sup_num_of_loops:                       111
% 3.27/1.00  sup_fw_superposition:                   130
% 3.27/1.00  sup_bw_superposition:                   80
% 3.27/1.00  sup_immediate_simplified:               74
% 3.27/1.00  sup_given_eliminated:                   0
% 3.27/1.00  comparisons_done:                       0
% 3.27/1.00  comparisons_avoided:                    53
% 3.27/1.00  
% 3.27/1.00  ------ Simplifications
% 3.27/1.00  
% 3.27/1.00  
% 3.27/1.00  sim_fw_subset_subsumed:                 33
% 3.27/1.00  sim_bw_subset_subsumed:                 22
% 3.27/1.00  sim_fw_subsumed:                        27
% 3.27/1.00  sim_bw_subsumed:                        0
% 3.27/1.00  sim_fw_subsumption_res:                 11
% 3.27/1.00  sim_bw_subsumption_res:                 0
% 3.27/1.00  sim_tautology_del:                      8
% 3.27/1.00  sim_eq_tautology_del:                   27
% 3.27/1.00  sim_eq_res_simp:                        0
% 3.27/1.00  sim_fw_demodulated:                     6
% 3.27/1.00  sim_bw_demodulated:                     29
% 3.27/1.00  sim_light_normalised:                   16
% 3.27/1.00  sim_joinable_taut:                      0
% 3.27/1.00  sim_joinable_simp:                      0
% 3.27/1.00  sim_ac_normalised:                      0
% 3.27/1.00  sim_smt_subsumption:                    0
% 3.27/1.00  
%------------------------------------------------------------------------------
