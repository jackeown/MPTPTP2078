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
% DateTime   : Thu Dec  3 12:05:10 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  158 (1003 expanded)
%              Number of clauses        :   80 ( 241 expanded)
%              Number of leaves         :   24 ( 246 expanded)
%              Depth                    :   20
%              Number of atoms          :  412 (2476 expanded)
%              Number of equality atoms :  200 (1163 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f50])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f86,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f58,f85])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f82,f86])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f47])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f61,f86,f86])).

fof(f84,plain,(
    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(definition_unfolding,[],[f84,f86,f86])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f74,f86,f86])).

fof(f80,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f81,f86])).

fof(f83,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1292,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1275,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_22,c_13])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_351,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_22,c_21,c_13])).

cnf(c_1274,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_1652,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_1275,c_1274])).

cnf(c_18,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1279,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2284,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_1279])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1456,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1457,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_2324,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2284,c_32,c_1457])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1286,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3472,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2324,c_1286])).

cnf(c_25,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_388,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_389,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_390,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_392,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_390])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1483,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_732,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1476,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != X0
    | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
    | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_1594,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
    | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3)
    | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_2292,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2284])).

cnf(c_740,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_1867,plain,
    ( k1_relat_1(sK3) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_2448,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1867])).

cnf(c_731,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2449,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_2953,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0))
    | k2_enumset1(X0,X0,X0,X0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2955,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2953])).

cnf(c_1647,plain,
    ( k1_relat_1(sK3) != X0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_3134,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_3684,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3472,c_27,c_32,c_25,c_392,c_1456,c_1457,c_1483,c_1594,c_2292,c_2448,c_2449,c_2955,c_3134])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1280,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3699,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3684,c_1280])).

cnf(c_4505,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3699,c_32,c_1457])).

cnf(c_1276,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2789,plain,
    ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1275,c_1276])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_367,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK1,sK1,sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_368,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_372,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_29,c_27,c_26])).

cnf(c_1273,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1278,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1725,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r1_tarski(k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3),k1_funct_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1273,c_1278])).

cnf(c_3138,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_funct_1(sK3,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2789,c_1725])).

cnf(c_4519,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4505,c_3138])).

cnf(c_14,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4545,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4519,c_14])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1285,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1283,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1840,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_1283])).

cnf(c_4662,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4545,c_1840])).

cnf(c_4666,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1292,c_4662])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1290,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2989,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_1290])).

cnf(c_1602,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0))
    | k2_enumset1(X0,X0,X0,X0) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1603,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(sK3)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1602])).

cnf(c_1605,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1603])).

cnf(c_3414,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2989,c_27,c_32,c_25,c_392,c_1457,c_1483,c_1594,c_1605,c_2284])).

cnf(c_3687,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3684,c_3414])).

cnf(c_4913,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4666,c_3687])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.88/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.88/0.99  
% 2.88/0.99  ------  iProver source info
% 2.88/0.99  
% 2.88/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.88/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.88/0.99  git: non_committed_changes: false
% 2.88/0.99  git: last_make_outside_of_git: false
% 2.88/0.99  
% 2.88/0.99  ------ 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options
% 2.88/0.99  
% 2.88/0.99  --out_options                           all
% 2.88/0.99  --tptp_safe_out                         true
% 2.88/0.99  --problem_path                          ""
% 2.88/0.99  --include_path                          ""
% 2.88/0.99  --clausifier                            res/vclausify_rel
% 2.88/0.99  --clausifier_options                    --mode clausify
% 2.88/0.99  --stdin                                 false
% 2.88/0.99  --stats_out                             all
% 2.88/0.99  
% 2.88/0.99  ------ General Options
% 2.88/0.99  
% 2.88/0.99  --fof                                   false
% 2.88/0.99  --time_out_real                         305.
% 2.88/0.99  --time_out_virtual                      -1.
% 2.88/0.99  --symbol_type_check                     false
% 2.88/0.99  --clausify_out                          false
% 2.88/0.99  --sig_cnt_out                           false
% 2.88/0.99  --trig_cnt_out                          false
% 2.88/0.99  --trig_cnt_out_tolerance                1.
% 2.88/0.99  --trig_cnt_out_sk_spl                   false
% 2.88/0.99  --abstr_cl_out                          false
% 2.88/0.99  
% 2.88/0.99  ------ Global Options
% 2.88/0.99  
% 2.88/0.99  --schedule                              default
% 2.88/0.99  --add_important_lit                     false
% 2.88/0.99  --prop_solver_per_cl                    1000
% 2.88/0.99  --min_unsat_core                        false
% 2.88/0.99  --soft_assumptions                      false
% 2.88/0.99  --soft_lemma_size                       3
% 2.88/0.99  --prop_impl_unit_size                   0
% 2.88/0.99  --prop_impl_unit                        []
% 2.88/0.99  --share_sel_clauses                     true
% 2.88/0.99  --reset_solvers                         false
% 2.88/0.99  --bc_imp_inh                            [conj_cone]
% 2.88/0.99  --conj_cone_tolerance                   3.
% 2.88/0.99  --extra_neg_conj                        none
% 2.88/0.99  --large_theory_mode                     true
% 2.88/0.99  --prolific_symb_bound                   200
% 2.88/0.99  --lt_threshold                          2000
% 2.88/0.99  --clause_weak_htbl                      true
% 2.88/0.99  --gc_record_bc_elim                     false
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing Options
% 2.88/0.99  
% 2.88/0.99  --preprocessing_flag                    true
% 2.88/0.99  --time_out_prep_mult                    0.1
% 2.88/0.99  --splitting_mode                        input
% 2.88/0.99  --splitting_grd                         true
% 2.88/0.99  --splitting_cvd                         false
% 2.88/0.99  --splitting_cvd_svl                     false
% 2.88/0.99  --splitting_nvd                         32
% 2.88/0.99  --sub_typing                            true
% 2.88/0.99  --prep_gs_sim                           true
% 2.88/0.99  --prep_unflatten                        true
% 2.88/0.99  --prep_res_sim                          true
% 2.88/0.99  --prep_upred                            true
% 2.88/0.99  --prep_sem_filter                       exhaustive
% 2.88/0.99  --prep_sem_filter_out                   false
% 2.88/0.99  --pred_elim                             true
% 2.88/0.99  --res_sim_input                         true
% 2.88/0.99  --eq_ax_congr_red                       true
% 2.88/0.99  --pure_diseq_elim                       true
% 2.88/0.99  --brand_transform                       false
% 2.88/0.99  --non_eq_to_eq                          false
% 2.88/0.99  --prep_def_merge                        true
% 2.88/0.99  --prep_def_merge_prop_impl              false
% 2.88/0.99  --prep_def_merge_mbd                    true
% 2.88/0.99  --prep_def_merge_tr_red                 false
% 2.88/0.99  --prep_def_merge_tr_cl                  false
% 2.88/0.99  --smt_preprocessing                     true
% 2.88/0.99  --smt_ac_axioms                         fast
% 2.88/0.99  --preprocessed_out                      false
% 2.88/0.99  --preprocessed_stats                    false
% 2.88/0.99  
% 2.88/0.99  ------ Abstraction refinement Options
% 2.88/0.99  
% 2.88/0.99  --abstr_ref                             []
% 2.88/0.99  --abstr_ref_prep                        false
% 2.88/0.99  --abstr_ref_until_sat                   false
% 2.88/0.99  --abstr_ref_sig_restrict                funpre
% 2.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.99  --abstr_ref_under                       []
% 2.88/0.99  
% 2.88/0.99  ------ SAT Options
% 2.88/0.99  
% 2.88/0.99  --sat_mode                              false
% 2.88/0.99  --sat_fm_restart_options                ""
% 2.88/0.99  --sat_gr_def                            false
% 2.88/0.99  --sat_epr_types                         true
% 2.88/0.99  --sat_non_cyclic_types                  false
% 2.88/0.99  --sat_finite_models                     false
% 2.88/0.99  --sat_fm_lemmas                         false
% 2.88/0.99  --sat_fm_prep                           false
% 2.88/0.99  --sat_fm_uc_incr                        true
% 2.88/0.99  --sat_out_model                         small
% 2.88/0.99  --sat_out_clauses                       false
% 2.88/0.99  
% 2.88/0.99  ------ QBF Options
% 2.88/0.99  
% 2.88/0.99  --qbf_mode                              false
% 2.88/0.99  --qbf_elim_univ                         false
% 2.88/0.99  --qbf_dom_inst                          none
% 2.88/0.99  --qbf_dom_pre_inst                      false
% 2.88/0.99  --qbf_sk_in                             false
% 2.88/0.99  --qbf_pred_elim                         true
% 2.88/0.99  --qbf_split                             512
% 2.88/0.99  
% 2.88/0.99  ------ BMC1 Options
% 2.88/0.99  
% 2.88/0.99  --bmc1_incremental                      false
% 2.88/0.99  --bmc1_axioms                           reachable_all
% 2.88/0.99  --bmc1_min_bound                        0
% 2.88/0.99  --bmc1_max_bound                        -1
% 2.88/0.99  --bmc1_max_bound_default                -1
% 2.88/0.99  --bmc1_symbol_reachability              true
% 2.88/0.99  --bmc1_property_lemmas                  false
% 2.88/0.99  --bmc1_k_induction                      false
% 2.88/0.99  --bmc1_non_equiv_states                 false
% 2.88/0.99  --bmc1_deadlock                         false
% 2.88/0.99  --bmc1_ucm                              false
% 2.88/0.99  --bmc1_add_unsat_core                   none
% 2.88/0.99  --bmc1_unsat_core_children              false
% 2.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.99  --bmc1_out_stat                         full
% 2.88/0.99  --bmc1_ground_init                      false
% 2.88/0.99  --bmc1_pre_inst_next_state              false
% 2.88/0.99  --bmc1_pre_inst_state                   false
% 2.88/0.99  --bmc1_pre_inst_reach_state             false
% 2.88/0.99  --bmc1_out_unsat_core                   false
% 2.88/0.99  --bmc1_aig_witness_out                  false
% 2.88/0.99  --bmc1_verbose                          false
% 2.88/0.99  --bmc1_dump_clauses_tptp                false
% 2.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.99  --bmc1_dump_file                        -
% 2.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.99  --bmc1_ucm_extend_mode                  1
% 2.88/0.99  --bmc1_ucm_init_mode                    2
% 2.88/0.99  --bmc1_ucm_cone_mode                    none
% 2.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.99  --bmc1_ucm_relax_model                  4
% 2.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.99  --bmc1_ucm_layered_model                none
% 2.88/0.99  --bmc1_ucm_max_lemma_size               10
% 2.88/0.99  
% 2.88/0.99  ------ AIG Options
% 2.88/0.99  
% 2.88/0.99  --aig_mode                              false
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation Options
% 2.88/0.99  
% 2.88/0.99  --instantiation_flag                    true
% 2.88/0.99  --inst_sos_flag                         false
% 2.88/0.99  --inst_sos_phase                        true
% 2.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel_side                     num_symb
% 2.88/0.99  --inst_solver_per_active                1400
% 2.88/0.99  --inst_solver_calls_frac                1.
% 2.88/0.99  --inst_passive_queue_type               priority_queues
% 2.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.99  --inst_passive_queues_freq              [25;2]
% 2.88/0.99  --inst_dismatching                      true
% 2.88/0.99  --inst_eager_unprocessed_to_passive     true
% 2.88/0.99  --inst_prop_sim_given                   true
% 2.88/0.99  --inst_prop_sim_new                     false
% 2.88/0.99  --inst_subs_new                         false
% 2.88/0.99  --inst_eq_res_simp                      false
% 2.88/0.99  --inst_subs_given                       false
% 2.88/0.99  --inst_orphan_elimination               true
% 2.88/0.99  --inst_learning_loop_flag               true
% 2.88/0.99  --inst_learning_start                   3000
% 2.88/0.99  --inst_learning_factor                  2
% 2.88/0.99  --inst_start_prop_sim_after_learn       3
% 2.88/0.99  --inst_sel_renew                        solver
% 2.88/0.99  --inst_lit_activity_flag                true
% 2.88/0.99  --inst_restr_to_given                   false
% 2.88/0.99  --inst_activity_threshold               500
% 2.88/0.99  --inst_out_proof                        true
% 2.88/0.99  
% 2.88/0.99  ------ Resolution Options
% 2.88/0.99  
% 2.88/0.99  --resolution_flag                       true
% 2.88/0.99  --res_lit_sel                           adaptive
% 2.88/0.99  --res_lit_sel_side                      none
% 2.88/0.99  --res_ordering                          kbo
% 2.88/0.99  --res_to_prop_solver                    active
% 2.88/0.99  --res_prop_simpl_new                    false
% 2.88/0.99  --res_prop_simpl_given                  true
% 2.88/0.99  --res_passive_queue_type                priority_queues
% 2.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.99  --res_passive_queues_freq               [15;5]
% 2.88/0.99  --res_forward_subs                      full
% 2.88/0.99  --res_backward_subs                     full
% 2.88/0.99  --res_forward_subs_resolution           true
% 2.88/0.99  --res_backward_subs_resolution          true
% 2.88/0.99  --res_orphan_elimination                true
% 2.88/0.99  --res_time_limit                        2.
% 2.88/0.99  --res_out_proof                         true
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Options
% 2.88/0.99  
% 2.88/0.99  --superposition_flag                    true
% 2.88/0.99  --sup_passive_queue_type                priority_queues
% 2.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.99  --demod_completeness_check              fast
% 2.88/0.99  --demod_use_ground                      true
% 2.88/0.99  --sup_to_prop_solver                    passive
% 2.88/0.99  --sup_prop_simpl_new                    true
% 2.88/0.99  --sup_prop_simpl_given                  true
% 2.88/0.99  --sup_fun_splitting                     false
% 2.88/0.99  --sup_smt_interval                      50000
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Simplification Setup
% 2.88/0.99  
% 2.88/0.99  --sup_indices_passive                   []
% 2.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_full_bw                           [BwDemod]
% 2.88/0.99  --sup_immed_triv                        [TrivRules]
% 2.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_immed_bw_main                     []
% 2.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  
% 2.88/0.99  ------ Combination Options
% 2.88/0.99  
% 2.88/0.99  --comb_res_mult                         3
% 2.88/0.99  --comb_sup_mult                         2
% 2.88/0.99  --comb_inst_mult                        10
% 2.88/0.99  
% 2.88/0.99  ------ Debug Options
% 2.88/0.99  
% 2.88/0.99  --dbg_backtrace                         false
% 2.88/0.99  --dbg_dump_prop_clauses                 false
% 2.88/0.99  --dbg_dump_prop_clauses_file            -
% 2.88/0.99  --dbg_out_stat                          false
% 2.88/0.99  ------ Parsing...
% 2.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.88/0.99  ------ Proving...
% 2.88/0.99  ------ Problem Properties 
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  clauses                                 26
% 2.88/0.99  conjectures                             3
% 2.88/0.99  EPR                                     5
% 2.88/0.99  Horn                                    24
% 2.88/0.99  unary                                   9
% 2.88/0.99  binary                                  10
% 2.88/0.99  lits                                    50
% 2.88/0.99  lits eq                                 15
% 2.88/0.99  fd_pure                                 0
% 2.88/0.99  fd_pseudo                               0
% 2.88/0.99  fd_cond                                 2
% 2.88/0.99  fd_pseudo_cond                          2
% 2.88/0.99  AC symbols                              0
% 2.88/0.99  
% 2.88/0.99  ------ Schedule dynamic 5 is on 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  ------ 
% 2.88/0.99  Current options:
% 2.88/0.99  ------ 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options
% 2.88/0.99  
% 2.88/0.99  --out_options                           all
% 2.88/0.99  --tptp_safe_out                         true
% 2.88/0.99  --problem_path                          ""
% 2.88/0.99  --include_path                          ""
% 2.88/0.99  --clausifier                            res/vclausify_rel
% 2.88/0.99  --clausifier_options                    --mode clausify
% 2.88/0.99  --stdin                                 false
% 2.88/0.99  --stats_out                             all
% 2.88/0.99  
% 2.88/0.99  ------ General Options
% 2.88/0.99  
% 2.88/0.99  --fof                                   false
% 2.88/0.99  --time_out_real                         305.
% 2.88/0.99  --time_out_virtual                      -1.
% 2.88/0.99  --symbol_type_check                     false
% 2.88/0.99  --clausify_out                          false
% 2.88/0.99  --sig_cnt_out                           false
% 2.88/0.99  --trig_cnt_out                          false
% 2.88/0.99  --trig_cnt_out_tolerance                1.
% 2.88/0.99  --trig_cnt_out_sk_spl                   false
% 2.88/0.99  --abstr_cl_out                          false
% 2.88/0.99  
% 2.88/0.99  ------ Global Options
% 2.88/0.99  
% 2.88/0.99  --schedule                              default
% 2.88/0.99  --add_important_lit                     false
% 2.88/0.99  --prop_solver_per_cl                    1000
% 2.88/0.99  --min_unsat_core                        false
% 2.88/0.99  --soft_assumptions                      false
% 2.88/0.99  --soft_lemma_size                       3
% 2.88/0.99  --prop_impl_unit_size                   0
% 2.88/0.99  --prop_impl_unit                        []
% 2.88/0.99  --share_sel_clauses                     true
% 2.88/0.99  --reset_solvers                         false
% 2.88/0.99  --bc_imp_inh                            [conj_cone]
% 2.88/0.99  --conj_cone_tolerance                   3.
% 2.88/0.99  --extra_neg_conj                        none
% 2.88/0.99  --large_theory_mode                     true
% 2.88/0.99  --prolific_symb_bound                   200
% 2.88/0.99  --lt_threshold                          2000
% 2.88/0.99  --clause_weak_htbl                      true
% 2.88/0.99  --gc_record_bc_elim                     false
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing Options
% 2.88/0.99  
% 2.88/0.99  --preprocessing_flag                    true
% 2.88/0.99  --time_out_prep_mult                    0.1
% 2.88/0.99  --splitting_mode                        input
% 2.88/0.99  --splitting_grd                         true
% 2.88/0.99  --splitting_cvd                         false
% 2.88/0.99  --splitting_cvd_svl                     false
% 2.88/0.99  --splitting_nvd                         32
% 2.88/0.99  --sub_typing                            true
% 2.88/0.99  --prep_gs_sim                           true
% 2.88/0.99  --prep_unflatten                        true
% 2.88/0.99  --prep_res_sim                          true
% 2.88/0.99  --prep_upred                            true
% 2.88/0.99  --prep_sem_filter                       exhaustive
% 2.88/0.99  --prep_sem_filter_out                   false
% 2.88/0.99  --pred_elim                             true
% 2.88/0.99  --res_sim_input                         true
% 2.88/1.00  --eq_ax_congr_red                       true
% 2.88/1.00  --pure_diseq_elim                       true
% 2.88/1.00  --brand_transform                       false
% 2.88/1.00  --non_eq_to_eq                          false
% 2.88/1.00  --prep_def_merge                        true
% 2.88/1.00  --prep_def_merge_prop_impl              false
% 2.88/1.00  --prep_def_merge_mbd                    true
% 2.88/1.00  --prep_def_merge_tr_red                 false
% 2.88/1.00  --prep_def_merge_tr_cl                  false
% 2.88/1.00  --smt_preprocessing                     true
% 2.88/1.00  --smt_ac_axioms                         fast
% 2.88/1.00  --preprocessed_out                      false
% 2.88/1.00  --preprocessed_stats                    false
% 2.88/1.00  
% 2.88/1.00  ------ Abstraction refinement Options
% 2.88/1.00  
% 2.88/1.00  --abstr_ref                             []
% 2.88/1.00  --abstr_ref_prep                        false
% 2.88/1.00  --abstr_ref_until_sat                   false
% 2.88/1.00  --abstr_ref_sig_restrict                funpre
% 2.88/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/1.00  --abstr_ref_under                       []
% 2.88/1.00  
% 2.88/1.00  ------ SAT Options
% 2.88/1.00  
% 2.88/1.00  --sat_mode                              false
% 2.88/1.00  --sat_fm_restart_options                ""
% 2.88/1.00  --sat_gr_def                            false
% 2.88/1.00  --sat_epr_types                         true
% 2.88/1.00  --sat_non_cyclic_types                  false
% 2.88/1.00  --sat_finite_models                     false
% 2.88/1.00  --sat_fm_lemmas                         false
% 2.88/1.00  --sat_fm_prep                           false
% 2.88/1.00  --sat_fm_uc_incr                        true
% 2.88/1.00  --sat_out_model                         small
% 2.88/1.00  --sat_out_clauses                       false
% 2.88/1.00  
% 2.88/1.00  ------ QBF Options
% 2.88/1.00  
% 2.88/1.00  --qbf_mode                              false
% 2.88/1.00  --qbf_elim_univ                         false
% 2.88/1.00  --qbf_dom_inst                          none
% 2.88/1.00  --qbf_dom_pre_inst                      false
% 2.88/1.00  --qbf_sk_in                             false
% 2.88/1.00  --qbf_pred_elim                         true
% 2.88/1.00  --qbf_split                             512
% 2.88/1.00  
% 2.88/1.00  ------ BMC1 Options
% 2.88/1.00  
% 2.88/1.00  --bmc1_incremental                      false
% 2.88/1.00  --bmc1_axioms                           reachable_all
% 2.88/1.00  --bmc1_min_bound                        0
% 2.88/1.00  --bmc1_max_bound                        -1
% 2.88/1.00  --bmc1_max_bound_default                -1
% 2.88/1.00  --bmc1_symbol_reachability              true
% 2.88/1.00  --bmc1_property_lemmas                  false
% 2.88/1.00  --bmc1_k_induction                      false
% 2.88/1.00  --bmc1_non_equiv_states                 false
% 2.88/1.00  --bmc1_deadlock                         false
% 2.88/1.00  --bmc1_ucm                              false
% 2.88/1.00  --bmc1_add_unsat_core                   none
% 2.88/1.00  --bmc1_unsat_core_children              false
% 2.88/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/1.00  --bmc1_out_stat                         full
% 2.88/1.00  --bmc1_ground_init                      false
% 2.88/1.00  --bmc1_pre_inst_next_state              false
% 2.88/1.00  --bmc1_pre_inst_state                   false
% 2.88/1.00  --bmc1_pre_inst_reach_state             false
% 2.88/1.00  --bmc1_out_unsat_core                   false
% 2.88/1.00  --bmc1_aig_witness_out                  false
% 2.88/1.00  --bmc1_verbose                          false
% 2.88/1.00  --bmc1_dump_clauses_tptp                false
% 2.88/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.88/1.00  --bmc1_dump_file                        -
% 2.88/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.88/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.88/1.00  --bmc1_ucm_extend_mode                  1
% 2.88/1.00  --bmc1_ucm_init_mode                    2
% 2.88/1.00  --bmc1_ucm_cone_mode                    none
% 2.88/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.88/1.00  --bmc1_ucm_relax_model                  4
% 2.88/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.88/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/1.00  --bmc1_ucm_layered_model                none
% 2.88/1.00  --bmc1_ucm_max_lemma_size               10
% 2.88/1.00  
% 2.88/1.00  ------ AIG Options
% 2.88/1.00  
% 2.88/1.00  --aig_mode                              false
% 2.88/1.00  
% 2.88/1.00  ------ Instantiation Options
% 2.88/1.00  
% 2.88/1.00  --instantiation_flag                    true
% 2.88/1.00  --inst_sos_flag                         false
% 2.88/1.00  --inst_sos_phase                        true
% 2.88/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/1.00  --inst_lit_sel_side                     none
% 2.88/1.00  --inst_solver_per_active                1400
% 2.88/1.00  --inst_solver_calls_frac                1.
% 2.88/1.00  --inst_passive_queue_type               priority_queues
% 2.88/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/1.00  --inst_passive_queues_freq              [25;2]
% 2.88/1.00  --inst_dismatching                      true
% 2.88/1.00  --inst_eager_unprocessed_to_passive     true
% 2.88/1.00  --inst_prop_sim_given                   true
% 2.88/1.00  --inst_prop_sim_new                     false
% 2.88/1.00  --inst_subs_new                         false
% 2.88/1.00  --inst_eq_res_simp                      false
% 2.88/1.00  --inst_subs_given                       false
% 2.88/1.00  --inst_orphan_elimination               true
% 2.88/1.00  --inst_learning_loop_flag               true
% 2.88/1.00  --inst_learning_start                   3000
% 2.88/1.00  --inst_learning_factor                  2
% 2.88/1.00  --inst_start_prop_sim_after_learn       3
% 2.88/1.00  --inst_sel_renew                        solver
% 2.88/1.00  --inst_lit_activity_flag                true
% 2.88/1.00  --inst_restr_to_given                   false
% 2.88/1.00  --inst_activity_threshold               500
% 2.88/1.00  --inst_out_proof                        true
% 2.88/1.00  
% 2.88/1.00  ------ Resolution Options
% 2.88/1.00  
% 2.88/1.00  --resolution_flag                       false
% 2.88/1.00  --res_lit_sel                           adaptive
% 2.88/1.00  --res_lit_sel_side                      none
% 2.88/1.00  --res_ordering                          kbo
% 2.88/1.00  --res_to_prop_solver                    active
% 2.88/1.00  --res_prop_simpl_new                    false
% 2.88/1.00  --res_prop_simpl_given                  true
% 2.88/1.00  --res_passive_queue_type                priority_queues
% 2.88/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/1.00  --res_passive_queues_freq               [15;5]
% 2.88/1.00  --res_forward_subs                      full
% 2.88/1.00  --res_backward_subs                     full
% 2.88/1.00  --res_forward_subs_resolution           true
% 2.88/1.00  --res_backward_subs_resolution          true
% 2.88/1.00  --res_orphan_elimination                true
% 2.88/1.00  --res_time_limit                        2.
% 2.88/1.00  --res_out_proof                         true
% 2.88/1.00  
% 2.88/1.00  ------ Superposition Options
% 2.88/1.00  
% 2.88/1.00  --superposition_flag                    true
% 2.88/1.00  --sup_passive_queue_type                priority_queues
% 2.88/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.88/1.00  --demod_completeness_check              fast
% 2.88/1.00  --demod_use_ground                      true
% 2.88/1.00  --sup_to_prop_solver                    passive
% 2.88/1.00  --sup_prop_simpl_new                    true
% 2.88/1.00  --sup_prop_simpl_given                  true
% 2.88/1.00  --sup_fun_splitting                     false
% 2.88/1.00  --sup_smt_interval                      50000
% 2.88/1.00  
% 2.88/1.00  ------ Superposition Simplification Setup
% 2.88/1.00  
% 2.88/1.00  --sup_indices_passive                   []
% 2.88/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.00  --sup_full_bw                           [BwDemod]
% 2.88/1.00  --sup_immed_triv                        [TrivRules]
% 2.88/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.00  --sup_immed_bw_main                     []
% 2.88/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/1.00  
% 2.88/1.00  ------ Combination Options
% 2.88/1.00  
% 2.88/1.00  --comb_res_mult                         3
% 2.88/1.00  --comb_sup_mult                         2
% 2.88/1.00  --comb_inst_mult                        10
% 2.88/1.00  
% 2.88/1.00  ------ Debug Options
% 2.88/1.00  
% 2.88/1.00  --dbg_backtrace                         false
% 2.88/1.00  --dbg_dump_prop_clauses                 false
% 2.88/1.00  --dbg_dump_prop_clauses_file            -
% 2.88/1.00  --dbg_out_stat                          false
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  ------ Proving...
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  % SZS status Theorem for theBenchmark.p
% 2.88/1.00  
% 2.88/1.00   Resolution empty clause
% 2.88/1.00  
% 2.88/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.88/1.00  
% 2.88/1.00  fof(f1,axiom,(
% 2.88/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f23,plain,(
% 2.88/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.88/1.00    inference(ennf_transformation,[],[f1])).
% 2.88/1.00  
% 2.88/1.00  fof(f41,plain,(
% 2.88/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.88/1.00    inference(nnf_transformation,[],[f23])).
% 2.88/1.00  
% 2.88/1.00  fof(f42,plain,(
% 2.88/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.88/1.00    inference(rectify,[],[f41])).
% 2.88/1.00  
% 2.88/1.00  fof(f43,plain,(
% 2.88/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.88/1.00    introduced(choice_axiom,[])).
% 2.88/1.00  
% 2.88/1.00  fof(f44,plain,(
% 2.88/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 2.88/1.00  
% 2.88/1.00  fof(f53,plain,(
% 2.88/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f44])).
% 2.88/1.00  
% 2.88/1.00  fof(f20,conjecture,(
% 2.88/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f21,negated_conjecture,(
% 2.88/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 2.88/1.00    inference(negated_conjecture,[],[f20])).
% 2.88/1.00  
% 2.88/1.00  fof(f39,plain,(
% 2.88/1.00    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.88/1.00    inference(ennf_transformation,[],[f21])).
% 2.88/1.00  
% 2.88/1.00  fof(f40,plain,(
% 2.88/1.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.88/1.00    inference(flattening,[],[f39])).
% 2.88/1.00  
% 2.88/1.00  fof(f50,plain,(
% 2.88/1.00    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 2.88/1.00    introduced(choice_axiom,[])).
% 2.88/1.00  
% 2.88/1.00  fof(f51,plain,(
% 2.88/1.00    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 2.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f50])).
% 2.88/1.00  
% 2.88/1.00  fof(f82,plain,(
% 2.88/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.88/1.00    inference(cnf_transformation,[],[f51])).
% 2.88/1.00  
% 2.88/1.00  fof(f3,axiom,(
% 2.88/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f58,plain,(
% 2.88/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f3])).
% 2.88/1.00  
% 2.88/1.00  fof(f4,axiom,(
% 2.88/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f59,plain,(
% 2.88/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f4])).
% 2.88/1.00  
% 2.88/1.00  fof(f5,axiom,(
% 2.88/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f60,plain,(
% 2.88/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f5])).
% 2.88/1.00  
% 2.88/1.00  fof(f85,plain,(
% 2.88/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.88/1.00    inference(definition_unfolding,[],[f59,f60])).
% 2.88/1.00  
% 2.88/1.00  fof(f86,plain,(
% 2.88/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.88/1.00    inference(definition_unfolding,[],[f58,f85])).
% 2.88/1.00  
% 2.88/1.00  fof(f92,plain,(
% 2.88/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 2.88/1.00    inference(definition_unfolding,[],[f82,f86])).
% 2.88/1.00  
% 2.88/1.00  fof(f17,axiom,(
% 2.88/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f22,plain,(
% 2.88/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.88/1.00    inference(pure_predicate_removal,[],[f17])).
% 2.88/1.00  
% 2.88/1.00  fof(f35,plain,(
% 2.88/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.00    inference(ennf_transformation,[],[f22])).
% 2.88/1.00  
% 2.88/1.00  fof(f77,plain,(
% 2.88/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/1.00    inference(cnf_transformation,[],[f35])).
% 2.88/1.00  
% 2.88/1.00  fof(f10,axiom,(
% 2.88/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f26,plain,(
% 2.88/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.88/1.00    inference(ennf_transformation,[],[f10])).
% 2.88/1.00  
% 2.88/1.00  fof(f27,plain,(
% 2.88/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.88/1.00    inference(flattening,[],[f26])).
% 2.88/1.00  
% 2.88/1.00  fof(f68,plain,(
% 2.88/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f27])).
% 2.88/1.00  
% 2.88/1.00  fof(f16,axiom,(
% 2.88/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f34,plain,(
% 2.88/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.00    inference(ennf_transformation,[],[f16])).
% 2.88/1.00  
% 2.88/1.00  fof(f76,plain,(
% 2.88/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/1.00    inference(cnf_transformation,[],[f34])).
% 2.88/1.00  
% 2.88/1.00  fof(f13,axiom,(
% 2.88/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f30,plain,(
% 2.88/1.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.88/1.00    inference(ennf_transformation,[],[f13])).
% 2.88/1.00  
% 2.88/1.00  fof(f73,plain,(
% 2.88/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f30])).
% 2.88/1.00  
% 2.88/1.00  fof(f6,axiom,(
% 2.88/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f47,plain,(
% 2.88/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.88/1.00    inference(nnf_transformation,[],[f6])).
% 2.88/1.00  
% 2.88/1.00  fof(f48,plain,(
% 2.88/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.88/1.00    inference(flattening,[],[f47])).
% 2.88/1.00  
% 2.88/1.00  fof(f61,plain,(
% 2.88/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.88/1.00    inference(cnf_transformation,[],[f48])).
% 2.88/1.00  
% 2.88/1.00  fof(f89,plain,(
% 2.88/1.00    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 2.88/1.00    inference(definition_unfolding,[],[f61,f86,f86])).
% 2.88/1.00  
% 2.88/1.00  fof(f84,plain,(
% 2.88/1.00    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)),
% 2.88/1.00    inference(cnf_transformation,[],[f51])).
% 2.88/1.00  
% 2.88/1.00  fof(f91,plain,(
% 2.88/1.00    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)),
% 2.88/1.00    inference(definition_unfolding,[],[f84,f86,f86])).
% 2.88/1.00  
% 2.88/1.00  fof(f14,axiom,(
% 2.88/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f31,plain,(
% 2.88/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.88/1.00    inference(ennf_transformation,[],[f14])).
% 2.88/1.00  
% 2.88/1.00  fof(f32,plain,(
% 2.88/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.88/1.00    inference(flattening,[],[f31])).
% 2.88/1.00  
% 2.88/1.00  fof(f74,plain,(
% 2.88/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f32])).
% 2.88/1.00  
% 2.88/1.00  fof(f90,plain,(
% 2.88/1.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.88/1.00    inference(definition_unfolding,[],[f74,f86,f86])).
% 2.88/1.00  
% 2.88/1.00  fof(f80,plain,(
% 2.88/1.00    v1_funct_1(sK3)),
% 2.88/1.00    inference(cnf_transformation,[],[f51])).
% 2.88/1.00  
% 2.88/1.00  fof(f18,axiom,(
% 2.88/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f36,plain,(
% 2.88/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.88/1.00    inference(ennf_transformation,[],[f18])).
% 2.88/1.00  
% 2.88/1.00  fof(f78,plain,(
% 2.88/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.88/1.00    inference(cnf_transformation,[],[f36])).
% 2.88/1.00  
% 2.88/1.00  fof(f12,axiom,(
% 2.88/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f28,plain,(
% 2.88/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.88/1.00    inference(ennf_transformation,[],[f12])).
% 2.88/1.00  
% 2.88/1.00  fof(f29,plain,(
% 2.88/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.88/1.00    inference(flattening,[],[f28])).
% 2.88/1.00  
% 2.88/1.00  fof(f71,plain,(
% 2.88/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f29])).
% 2.88/1.00  
% 2.88/1.00  fof(f19,axiom,(
% 2.88/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f37,plain,(
% 2.88/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.88/1.00    inference(ennf_transformation,[],[f19])).
% 2.88/1.00  
% 2.88/1.00  fof(f38,plain,(
% 2.88/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.88/1.00    inference(flattening,[],[f37])).
% 2.88/1.00  
% 2.88/1.00  fof(f79,plain,(
% 2.88/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f38])).
% 2.88/1.00  
% 2.88/1.00  fof(f81,plain,(
% 2.88/1.00    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 2.88/1.00    inference(cnf_transformation,[],[f51])).
% 2.88/1.00  
% 2.88/1.00  fof(f93,plain,(
% 2.88/1.00    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 2.88/1.00    inference(definition_unfolding,[],[f81,f86])).
% 2.88/1.00  
% 2.88/1.00  fof(f83,plain,(
% 2.88/1.00    k1_xboole_0 != sK2),
% 2.88/1.00    inference(cnf_transformation,[],[f51])).
% 2.88/1.00  
% 2.88/1.00  fof(f15,axiom,(
% 2.88/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f33,plain,(
% 2.88/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.88/1.00    inference(ennf_transformation,[],[f15])).
% 2.88/1.00  
% 2.88/1.00  fof(f75,plain,(
% 2.88/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f33])).
% 2.88/1.00  
% 2.88/1.00  fof(f11,axiom,(
% 2.88/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f70,plain,(
% 2.88/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.88/1.00    inference(cnf_transformation,[],[f11])).
% 2.88/1.00  
% 2.88/1.00  fof(f7,axiom,(
% 2.88/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f64,plain,(
% 2.88/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.88/1.00    inference(cnf_transformation,[],[f7])).
% 2.88/1.00  
% 2.88/1.00  fof(f8,axiom,(
% 2.88/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f49,plain,(
% 2.88/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.88/1.00    inference(nnf_transformation,[],[f8])).
% 2.88/1.00  
% 2.88/1.00  fof(f65,plain,(
% 2.88/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.88/1.00    inference(cnf_transformation,[],[f49])).
% 2.88/1.00  
% 2.88/1.00  fof(f2,axiom,(
% 2.88/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/1.00  
% 2.88/1.00  fof(f45,plain,(
% 2.88/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.88/1.00    inference(nnf_transformation,[],[f2])).
% 2.88/1.00  
% 2.88/1.00  fof(f46,plain,(
% 2.88/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.88/1.00    inference(flattening,[],[f45])).
% 2.88/1.00  
% 2.88/1.00  fof(f57,plain,(
% 2.88/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.88/1.00    inference(cnf_transformation,[],[f46])).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1,plain,
% 2.88/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.88/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1292,plain,
% 2.88/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.88/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_27,negated_conjecture,
% 2.88/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 2.88/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1275,plain,
% 2.88/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_22,plain,
% 2.88/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.88/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_13,plain,
% 2.88/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_347,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | ~ v1_relat_1(X0)
% 2.88/1.00      | k7_relat_1(X0,X1) = X0 ),
% 2.88/1.00      inference(resolution,[status(thm)],[c_22,c_13]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_21,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_351,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | k7_relat_1(X0,X1) = X0 ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_347,c_22,c_21,c_13]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1274,plain,
% 2.88/1.00      ( k7_relat_1(X0,X1) = X0
% 2.88/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1652,plain,
% 2.88/1.00      ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = sK3 ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1275,c_1274]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_18,plain,
% 2.88/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1279,plain,
% 2.88/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 2.88/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2284,plain,
% 2.88/1.00      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
% 2.88/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1652,c_1279]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_32,plain,
% 2.88/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1456,plain,
% 2.88/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 2.88/1.00      | v1_relat_1(sK3) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1457,plain,
% 2.88/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) != iProver_top
% 2.88/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2324,plain,
% 2.88/1.00      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_2284,c_32,c_1457]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_8,plain,
% 2.88/1.00      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 2.88/1.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.88/1.00      | k1_xboole_0 = X0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1286,plain,
% 2.88/1.00      ( k2_enumset1(X0,X0,X0,X0) = X1
% 2.88/1.00      | k1_xboole_0 = X1
% 2.88/1.00      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3472,plain,
% 2.88/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 2.88/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_2324,c_1286]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_25,negated_conjecture,
% 2.88/1.00      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
% 2.88/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_19,plain,
% 2.88/1.00      ( ~ v1_funct_1(X0)
% 2.88/1.00      | ~ v1_relat_1(X0)
% 2.88/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.88/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_29,negated_conjecture,
% 2.88/1.00      ( v1_funct_1(sK3) ),
% 2.88/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_388,plain,
% 2.88/1.00      ( ~ v1_relat_1(X0)
% 2.88/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.88/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.88/1.00      | sK3 != X0 ),
% 2.88/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_389,plain,
% 2.88/1.00      ( ~ v1_relat_1(sK3)
% 2.88/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.88/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.88/1.00      inference(unflattening,[status(thm)],[c_388]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_390,plain,
% 2.88/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.88/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.88/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_392,plain,
% 2.88/1.00      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
% 2.88/1.00      | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK3)
% 2.88/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_390]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_23,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1483,plain,
% 2.88/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 2.88/1.00      | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_732,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1476,plain,
% 2.88/1.00      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != X0
% 2.88/1.00      | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
% 2.88/1.00      | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != X0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_732]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1594,plain,
% 2.88/1.00      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
% 2.88/1.00      | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3)
% 2.88/1.00      | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != k2_relat_1(sK3) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_1476]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2292,plain,
% 2.88/1.00      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
% 2.88/1.00      | ~ v1_relat_1(sK3) ),
% 2.88/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2284]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_740,plain,
% 2.88/1.00      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 2.88/1.00      theory(equality) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1867,plain,
% 2.88/1.00      ( k1_relat_1(sK3) = k1_relat_1(X0) | sK3 != X0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_740]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2448,plain,
% 2.88/1.00      ( k1_relat_1(sK3) = k1_relat_1(sK3) | sK3 != sK3 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_1867]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_731,plain,( X0 = X0 ),theory(equality) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2449,plain,
% 2.88/1.00      ( sK3 = sK3 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_731]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2953,plain,
% 2.88/1.00      ( ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0))
% 2.88/1.00      | k2_enumset1(X0,X0,X0,X0) = k1_relat_1(sK3)
% 2.88/1.00      | k1_xboole_0 = k1_relat_1(sK3) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2955,plain,
% 2.88/1.00      ( ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
% 2.88/1.00      | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 2.88/1.00      | k1_xboole_0 = k1_relat_1(sK3) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_2953]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1647,plain,
% 2.88/1.00      ( k1_relat_1(sK3) != X0
% 2.88/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 2.88/1.00      | k1_xboole_0 != X0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_732]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3134,plain,
% 2.88/1.00      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 2.88/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 2.88/1.00      | k1_xboole_0 != k1_relat_1(sK3) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_1647]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3684,plain,
% 2.88/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_3472,c_27,c_32,c_25,c_392,c_1456,c_1457,c_1483,c_1594,
% 2.88/1.00                 c_2292,c_2448,c_2449,c_2955,c_3134]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_17,plain,
% 2.88/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1280,plain,
% 2.88/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 2.88/1.00      | k1_xboole_0 = X0
% 2.88/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3699,plain,
% 2.88/1.00      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_3684,c_1280]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4505,plain,
% 2.88/1.00      ( sK3 = k1_xboole_0 ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_3699,c_32,c_1457]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1276,plain,
% 2.88/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.88/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2789,plain,
% 2.88/1.00      ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1275,c_1276]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_24,plain,
% 2.88/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.88/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | ~ r2_hidden(X3,X1)
% 2.88/1.00      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.88/1.00      | ~ v1_funct_1(X0)
% 2.88/1.00      | k1_xboole_0 = X2 ),
% 2.88/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_28,negated_conjecture,
% 2.88/1.00      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 2.88/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_367,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.88/1.00      | ~ r2_hidden(X3,X1)
% 2.88/1.00      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.88/1.00      | ~ v1_funct_1(X0)
% 2.88/1.00      | k2_enumset1(sK1,sK1,sK1,sK1) != X1
% 2.88/1.00      | sK2 != X2
% 2.88/1.00      | sK3 != X0
% 2.88/1.00      | k1_xboole_0 = X2 ),
% 2.88/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_368,plain,
% 2.88/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 2.88/1.00      | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 2.88/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3))
% 2.88/1.00      | ~ v1_funct_1(sK3)
% 2.88/1.00      | k1_xboole_0 = sK2 ),
% 2.88/1.00      inference(unflattening,[status(thm)],[c_367]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_26,negated_conjecture,
% 2.88/1.00      ( k1_xboole_0 != sK2 ),
% 2.88/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_372,plain,
% 2.88/1.00      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 2.88/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_368,c_29,c_27,c_26]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1273,plain,
% 2.88/1.00      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 2.88/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_20,plain,
% 2.88/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1278,plain,
% 2.88/1.00      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1725,plain,
% 2.88/1.00      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 2.88/1.00      | r1_tarski(k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3),k1_funct_1(sK3,X0)) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1273,c_1278]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3138,plain,
% 2.88/1.00      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 2.88/1.00      | r1_tarski(k2_relat_1(sK3),k1_funct_1(sK3,X0)) != iProver_top ),
% 2.88/1.00      inference(demodulation,[status(thm)],[c_2789,c_1725]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4519,plain,
% 2.88/1.00      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 2.88/1.00      | r1_tarski(k2_relat_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) != iProver_top ),
% 2.88/1.00      inference(demodulation,[status(thm)],[c_4505,c_3138]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_14,plain,
% 2.88/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4545,plain,
% 2.88/1.00      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 2.88/1.00      | r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,X0)) != iProver_top ),
% 2.88/1.00      inference(light_normalisation,[status(thm)],[c_4519,c_14]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_9,plain,
% 2.88/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.88/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1285,plain,
% 2.88/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_11,plain,
% 2.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.88/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1283,plain,
% 2.88/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.88/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1840,plain,
% 2.88/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1285,c_1283]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4662,plain,
% 2.88/1.00      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
% 2.88/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4545,c_1840]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4666,plain,
% 2.88/1.00      ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1292,c_4662]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3,plain,
% 2.88/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1290,plain,
% 2.88/1.00      ( X0 = X1
% 2.88/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.88/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2989,plain,
% 2.88/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 2.88/1.00      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_2324,c_1290]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1602,plain,
% 2.88/1.00      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK3))
% 2.88/1.00      | ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0))
% 2.88/1.00      | k2_enumset1(X0,X0,X0,X0) = k1_relat_1(sK3) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1603,plain,
% 2.88/1.00      ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(sK3)
% 2.88/1.00      | r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK3)) != iProver_top
% 2.88/1.00      | r1_tarski(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1602]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1605,plain,
% 2.88/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 2.88/1.00      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top
% 2.88/1.00      | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_1603]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3414,plain,
% 2.88/1.00      ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_2989,c_27,c_32,c_25,c_392,c_1457,c_1483,c_1594,c_1605,
% 2.88/1.00                 c_2284]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3687,plain,
% 2.88/1.00      ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) != iProver_top ),
% 2.88/1.00      inference(demodulation,[status(thm)],[c_3684,c_3414]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_4913,plain,
% 2.88/1.00      ( $false ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_4666,c_3687]) ).
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.88/1.00  
% 2.88/1.00  ------                               Statistics
% 2.88/1.00  
% 2.88/1.00  ------ General
% 2.88/1.00  
% 2.88/1.00  abstr_ref_over_cycles:                  0
% 2.88/1.00  abstr_ref_under_cycles:                 0
% 2.88/1.00  gc_basic_clause_elim:                   0
% 2.88/1.00  forced_gc_time:                         0
% 2.88/1.00  parsing_time:                           0.009
% 2.88/1.00  unif_index_cands_time:                  0.
% 2.88/1.00  unif_index_add_time:                    0.
% 2.88/1.00  orderings_time:                         0.
% 2.88/1.00  out_proof_time:                         0.01
% 2.88/1.00  total_time:                             0.175
% 2.88/1.00  num_of_symbols:                         51
% 2.88/1.00  num_of_terms:                           4593
% 2.88/1.00  
% 2.88/1.00  ------ Preprocessing
% 2.88/1.00  
% 2.88/1.00  num_of_splits:                          0
% 2.88/1.00  num_of_split_atoms:                     0
% 2.88/1.00  num_of_reused_defs:                     0
% 2.88/1.00  num_eq_ax_congr_red:                    15
% 2.88/1.00  num_of_sem_filtered_clauses:            1
% 2.88/1.00  num_of_subtypes:                        0
% 2.88/1.00  monotx_restored_types:                  0
% 2.88/1.00  sat_num_of_epr_types:                   0
% 2.88/1.00  sat_num_of_non_cyclic_types:            0
% 2.88/1.00  sat_guarded_non_collapsed_types:        0
% 2.88/1.00  num_pure_diseq_elim:                    0
% 2.88/1.00  simp_replaced_by:                       0
% 2.88/1.00  res_preprocessed:                       134
% 2.88/1.00  prep_upred:                             0
% 2.88/1.00  prep_unflattend:                        6
% 2.88/1.00  smt_new_axioms:                         0
% 2.88/1.00  pred_elim_cands:                        4
% 2.88/1.00  pred_elim:                              3
% 2.88/1.00  pred_elim_cl:                           3
% 2.88/1.00  pred_elim_cycles:                       5
% 2.88/1.00  merged_defs:                            8
% 2.88/1.00  merged_defs_ncl:                        0
% 2.88/1.00  bin_hyper_res:                          8
% 2.88/1.00  prep_cycles:                            4
% 2.88/1.00  pred_elim_time:                         0.004
% 2.88/1.00  splitting_time:                         0.
% 2.88/1.00  sem_filter_time:                        0.
% 2.88/1.00  monotx_time:                            0.
% 2.88/1.00  subtype_inf_time:                       0.
% 2.88/1.00  
% 2.88/1.00  ------ Problem properties
% 2.88/1.00  
% 2.88/1.00  clauses:                                26
% 2.88/1.00  conjectures:                            3
% 2.88/1.00  epr:                                    5
% 2.88/1.00  horn:                                   24
% 2.88/1.00  ground:                                 5
% 2.88/1.00  unary:                                  9
% 2.88/1.00  binary:                                 10
% 2.88/1.00  lits:                                   50
% 2.88/1.00  lits_eq:                                15
% 2.88/1.00  fd_pure:                                0
% 2.88/1.00  fd_pseudo:                              0
% 2.88/1.00  fd_cond:                                2
% 2.88/1.00  fd_pseudo_cond:                         2
% 2.88/1.00  ac_symbols:                             0
% 2.88/1.00  
% 2.88/1.00  ------ Propositional Solver
% 2.88/1.00  
% 2.88/1.00  prop_solver_calls:                      28
% 2.88/1.00  prop_fast_solver_calls:                 786
% 2.88/1.00  smt_solver_calls:                       0
% 2.88/1.00  smt_fast_solver_calls:                  0
% 2.88/1.00  prop_num_of_clauses:                    1901
% 2.88/1.00  prop_preprocess_simplified:             5506
% 2.88/1.00  prop_fo_subsumed:                       22
% 2.88/1.00  prop_solver_time:                       0.
% 2.88/1.00  smt_solver_time:                        0.
% 2.88/1.00  smt_fast_solver_time:                   0.
% 2.88/1.00  prop_fast_solver_time:                  0.
% 2.88/1.00  prop_unsat_core_time:                   0.
% 2.88/1.00  
% 2.88/1.00  ------ QBF
% 2.88/1.00  
% 2.88/1.00  qbf_q_res:                              0
% 2.88/1.00  qbf_num_tautologies:                    0
% 2.88/1.00  qbf_prep_cycles:                        0
% 2.88/1.00  
% 2.88/1.00  ------ BMC1
% 2.88/1.00  
% 2.88/1.00  bmc1_current_bound:                     -1
% 2.88/1.00  bmc1_last_solved_bound:                 -1
% 2.88/1.00  bmc1_unsat_core_size:                   -1
% 2.88/1.00  bmc1_unsat_core_parents_size:           -1
% 2.88/1.00  bmc1_merge_next_fun:                    0
% 2.88/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.88/1.00  
% 2.88/1.00  ------ Instantiation
% 2.88/1.00  
% 2.88/1.00  inst_num_of_clauses:                    550
% 2.88/1.00  inst_num_in_passive:                    65
% 2.88/1.00  inst_num_in_active:                     270
% 2.88/1.00  inst_num_in_unprocessed:                215
% 2.88/1.00  inst_num_of_loops:                      350
% 2.88/1.00  inst_num_of_learning_restarts:          0
% 2.88/1.00  inst_num_moves_active_passive:          77
% 2.88/1.00  inst_lit_activity:                      0
% 2.88/1.00  inst_lit_activity_moves:                0
% 2.88/1.00  inst_num_tautologies:                   0
% 2.88/1.00  inst_num_prop_implied:                  0
% 2.88/1.00  inst_num_existing_simplified:           0
% 2.88/1.00  inst_num_eq_res_simplified:             0
% 2.88/1.00  inst_num_child_elim:                    0
% 2.88/1.00  inst_num_of_dismatching_blockings:      141
% 2.88/1.00  inst_num_of_non_proper_insts:           527
% 2.88/1.00  inst_num_of_duplicates:                 0
% 2.88/1.00  inst_inst_num_from_inst_to_res:         0
% 2.88/1.00  inst_dismatching_checking_time:         0.
% 2.88/1.00  
% 2.88/1.00  ------ Resolution
% 2.88/1.00  
% 2.88/1.00  res_num_of_clauses:                     0
% 2.88/1.00  res_num_in_passive:                     0
% 2.88/1.00  res_num_in_active:                      0
% 2.88/1.00  res_num_of_loops:                       138
% 2.88/1.00  res_forward_subset_subsumed:            57
% 2.88/1.00  res_backward_subset_subsumed:           2
% 2.88/1.00  res_forward_subsumed:                   0
% 2.88/1.00  res_backward_subsumed:                  0
% 2.88/1.00  res_forward_subsumption_resolution:     0
% 2.88/1.00  res_backward_subsumption_resolution:    0
% 2.88/1.00  res_clause_to_clause_subsumption:       267
% 2.88/1.00  res_orphan_elimination:                 0
% 2.88/1.00  res_tautology_del:                      48
% 2.88/1.00  res_num_eq_res_simplified:              0
% 2.88/1.00  res_num_sel_changes:                    0
% 2.88/1.00  res_moves_from_active_to_pass:          0
% 2.88/1.00  
% 2.88/1.00  ------ Superposition
% 2.88/1.00  
% 2.88/1.00  sup_time_total:                         0.
% 2.88/1.00  sup_time_generating:                    0.
% 2.88/1.00  sup_time_sim_full:                      0.
% 2.88/1.00  sup_time_sim_immed:                     0.
% 2.88/1.00  
% 2.88/1.00  sup_num_of_clauses:                     56
% 2.88/1.00  sup_num_in_active:                      43
% 2.88/1.00  sup_num_in_passive:                     13
% 2.88/1.00  sup_num_of_loops:                       69
% 2.88/1.00  sup_fw_superposition:                   60
% 2.88/1.00  sup_bw_superposition:                   25
% 2.88/1.00  sup_immediate_simplified:               25
% 2.88/1.00  sup_given_eliminated:                   0
% 2.88/1.00  comparisons_done:                       0
% 2.88/1.00  comparisons_avoided:                    0
% 2.88/1.00  
% 2.88/1.00  ------ Simplifications
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  sim_fw_subset_subsumed:                 2
% 2.88/1.00  sim_bw_subset_subsumed:                 4
% 2.88/1.00  sim_fw_subsumed:                        9
% 2.88/1.00  sim_bw_subsumed:                        0
% 2.88/1.00  sim_fw_subsumption_res:                 2
% 2.88/1.00  sim_bw_subsumption_res:                 0
% 2.88/1.00  sim_tautology_del:                      2
% 2.88/1.00  sim_eq_tautology_del:                   9
% 2.88/1.00  sim_eq_res_simp:                        0
% 2.88/1.00  sim_fw_demodulated:                     3
% 2.88/1.00  sim_bw_demodulated:                     26
% 2.88/1.00  sim_light_normalised:                   16
% 2.88/1.00  sim_joinable_taut:                      0
% 2.88/1.00  sim_joinable_simp:                      0
% 2.88/1.00  sim_ac_normalised:                      0
% 2.88/1.00  sim_smt_subsumption:                    0
% 2.88/1.00  
%------------------------------------------------------------------------------
