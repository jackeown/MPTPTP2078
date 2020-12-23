%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:07 EST 2020

% Result     : Theorem 19.65s
% Output     : CNFRefutation 19.65s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 843 expanded)
%              Number of clauses        :  130 ( 250 expanded)
%              Number of leaves         :   28 ( 200 expanded)
%              Depth                    :   20
%              Number of atoms          :  564 (2052 expanded)
%              Number of equality atoms :  297 ( 978 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f57,plain,
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

fof(f58,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f45,f57])).

fof(f98,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f101,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f102,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f101])).

fof(f108,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f98,f102])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f52])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f70,f102,f102])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f96,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f107,plain,(
    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(definition_unfolding,[],[f100,f102,f102])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f82,f102,f102])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f97,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f109,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f97,f102])).

fof(f99,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f58])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1447,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1459,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2807,plain,
    ( v4_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1447,c_1459])).

cnf(c_17,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1464,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1470,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1476,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1475,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1999,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1476,c_1475])).

cnf(c_5637,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | o_0_0_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1470,c_1999])).

cnf(c_5645,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(X1)
    | k1_relat_1(X1) = o_0_0_xboole_0
    | v4_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_5637])).

cnf(c_44291,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = o_0_0_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2807,c_5645])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1766,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_44359,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_44291])).

cnf(c_45733,plain,
    ( k1_relat_1(sK3) = o_0_0_xboole_0
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44291,c_36,c_1766,c_44359])).

cnf(c_45734,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = o_0_0_xboole_0 ),
    inference(renaming,[status(thm)],[c_45733])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1467,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2004,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1447,c_1467])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1478,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_12,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_258,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_12])).

cnf(c_259,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_324,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_15,c_259])).

cnf(c_1444,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_13781,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_1444])).

cnf(c_13990,plain,
    ( r1_tarski(sK3,X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2004,c_13781])).

cnf(c_45748,plain,
    ( k1_relat_1(sK3) = o_0_0_xboole_0
    | r1_tarski(sK3,X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_45734,c_13990])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_11,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_108,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1767,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1766])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1956,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_657,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2082,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_2307,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2308,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2307])).

cnf(c_2737,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1457,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3395,plain,
    ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1447,c_1457])).

cnf(c_34,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_3527,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3395,c_34])).

cnf(c_658,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2173,plain,
    ( k1_relat_1(sK3) != X0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_3599,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2173])).

cnf(c_3600,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_2387,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_3948,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_3949,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3948])).

cnf(c_664,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1845,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
    | X1 != k1_zfmisc_1(X2)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_664])).

cnf(c_2736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | X0 != k1_xboole_0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1845])).

cnf(c_4522,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2736])).

cnf(c_4523,plain,
    ( k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4522])).

cnf(c_7692,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_661,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1803,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | X0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_661])).

cnf(c_49828,plain,
    ( v1_xboole_0(k1_relat_1(sK3))
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_relat_1(sK3) != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1803])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1955,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_61586,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1955])).

cnf(c_61802,plain,
    ( r1_tarski(sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_45748,c_38,c_36,c_41,c_108,c_3,c_1766,c_1767,c_1956,c_2082,c_2308,c_2737,c_3527,c_3599,c_3600,c_3949,c_4523,c_7692,c_44291,c_49828,c_61586])).

cnf(c_1469,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2003,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_1467])).

cnf(c_2341,plain,
    ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2003,c_1999])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1474,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3513,plain,
    ( o_0_0_xboole_0 = X0
    | r1_tarski(X0,o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2341,c_1474])).

cnf(c_61820,plain,
    ( sK3 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_61802,c_3513])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1455,plain,
    ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6875,plain,
    ( k8_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k2_enumset1(sK1,sK1,sK1,sK1))) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1447,c_1455])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1448,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1921,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK2 = k1_xboole_0
    | v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1447,c_1448])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_40,plain,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_103,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_109,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_125,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1801,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_1802,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1801])).

cnf(c_2201,plain,
    ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1921,c_40,c_35,c_103,c_109,c_125,c_1802])).

cnf(c_6885,plain,
    ( k8_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k2_enumset1(sK1,sK1,sK1,sK1))) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_6875,c_2201])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1456,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4133,plain,
    ( k8_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1447,c_1456])).

cnf(c_7479,plain,
    ( k10_relat_1(sK3,k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k2_enumset1(sK1,sK1,sK1,sK1))) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_6885,c_4133])).

cnf(c_87462,plain,
    ( k10_relat_1(o_0_0_xboole_0,k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,o_0_0_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_61820,c_7479])).

cnf(c_2208,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1999,c_1469])).

cnf(c_4134,plain,
    ( k8_relset_1(X0,X1,o_0_0_xboole_0,X2) = k10_relat_1(o_0_0_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_2208,c_1456])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1458,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5454,plain,
    ( m1_subset_1(k10_relat_1(o_0_0_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top
    | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4134,c_1458])).

cnf(c_10144,plain,
    ( m1_subset_1(k10_relat_1(o_0_0_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5454,c_2208])).

cnf(c_89628,plain,
    ( m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_87462,c_10144])).

cnf(c_89790,plain,
    ( m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_89628])).

cnf(c_12606,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_12617,plain,
    ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12606])).

cnf(c_12619,plain,
    ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12617])).

cnf(c_6236,plain,
    ( ~ m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(X0))
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_6237,plain,
    ( m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6236])).

cnf(c_6239,plain,
    ( m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6237])).

cnf(c_5585,plain,
    ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)),k2_enumset1(sK1,sK1,sK1,sK1))
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5589,plain,
    ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5585])).

cnf(c_2448,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0))
    | k2_enumset1(X0,X0,X0,X0) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4262,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
    | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2448])).

cnf(c_4263,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4262])).

cnf(c_1953,plain,
    ( ~ v4_relat_1(sK3,X0)
    | r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2282,plain,
    ( ~ v4_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))
    | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1953])).

cnf(c_2283,plain,
    ( v4_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2282])).

cnf(c_1807,plain,
    ( X0 != o_0_0_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1803])).

cnf(c_1809,plain,
    ( k1_xboole_0 != o_0_0_xboole_0
    | v1_xboole_0(k1_xboole_0) = iProver_top
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1807])).

cnf(c_1804,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | k1_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1777,plain,
    ( v4_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1778,plain,
    ( v4_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1777])).

cnf(c_130,plain,
    ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_89790,c_61586,c_12619,c_6239,c_5589,c_4263,c_3527,c_2283,c_1809,c_1804,c_1778,c_1767,c_1766,c_130,c_3,c_41,c_36,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.65/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.65/2.99  
% 19.65/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.65/2.99  
% 19.65/2.99  ------  iProver source info
% 19.65/2.99  
% 19.65/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.65/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.65/2.99  git: non_committed_changes: false
% 19.65/2.99  git: last_make_outside_of_git: false
% 19.65/2.99  
% 19.65/2.99  ------ 
% 19.65/2.99  ------ Parsing...
% 19.65/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.65/2.99  
% 19.65/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 19.65/2.99  
% 19.65/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.65/2.99  
% 19.65/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.65/2.99  ------ Proving...
% 19.65/2.99  ------ Problem Properties 
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  clauses                                 38
% 19.65/2.99  conjectures                             5
% 19.65/2.99  EPR                                     8
% 19.65/2.99  Horn                                    32
% 19.65/2.99  unary                                   10
% 19.65/2.99  binary                                  12
% 19.65/2.99  lits                                    86
% 19.65/2.99  lits eq                                 25
% 19.65/2.99  fd_pure                                 0
% 19.65/2.99  fd_pseudo                               0
% 19.65/2.99  fd_cond                                 6
% 19.65/2.99  fd_pseudo_cond                          2
% 19.65/2.99  AC symbols                              0
% 19.65/2.99  
% 19.65/2.99  ------ Input Options Time Limit: Unbounded
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  ------ 
% 19.65/2.99  Current options:
% 19.65/2.99  ------ 
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  ------ Proving...
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  % SZS status Theorem for theBenchmark.p
% 19.65/2.99  
% 19.65/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.65/2.99  
% 19.65/2.99  fof(f23,conjecture,(
% 19.65/2.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f24,negated_conjecture,(
% 19.65/2.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 19.65/2.99    inference(negated_conjecture,[],[f23])).
% 19.65/2.99  
% 19.65/2.99  fof(f44,plain,(
% 19.65/2.99    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 19.65/2.99    inference(ennf_transformation,[],[f24])).
% 19.65/2.99  
% 19.65/2.99  fof(f45,plain,(
% 19.65/2.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 19.65/2.99    inference(flattening,[],[f44])).
% 19.65/2.99  
% 19.65/2.99  fof(f57,plain,(
% 19.65/2.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 19.65/2.99    introduced(choice_axiom,[])).
% 19.65/2.99  
% 19.65/2.99  fof(f58,plain,(
% 19.65/2.99    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 19.65/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f45,f57])).
% 19.65/2.99  
% 19.65/2.99  fof(f98,plain,(
% 19.65/2.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 19.65/2.99    inference(cnf_transformation,[],[f58])).
% 19.65/2.99  
% 19.65/2.99  fof(f5,axiom,(
% 19.65/2.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f67,plain,(
% 19.65/2.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f5])).
% 19.65/2.99  
% 19.65/2.99  fof(f6,axiom,(
% 19.65/2.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f68,plain,(
% 19.65/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f6])).
% 19.65/2.99  
% 19.65/2.99  fof(f7,axiom,(
% 19.65/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f69,plain,(
% 19.65/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f7])).
% 19.65/2.99  
% 19.65/2.99  fof(f101,plain,(
% 19.65/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.65/2.99    inference(definition_unfolding,[],[f68,f69])).
% 19.65/2.99  
% 19.65/2.99  fof(f102,plain,(
% 19.65/2.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 19.65/2.99    inference(definition_unfolding,[],[f67,f101])).
% 19.65/2.99  
% 19.65/2.99  fof(f108,plain,(
% 19.65/2.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 19.65/2.99    inference(definition_unfolding,[],[f98,f102])).
% 19.65/2.99  
% 19.65/2.99  fof(f17,axiom,(
% 19.65/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f25,plain,(
% 19.65/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 19.65/2.99    inference(pure_predicate_removal,[],[f17])).
% 19.65/2.99  
% 19.65/2.99  fof(f37,plain,(
% 19.65/2.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.65/2.99    inference(ennf_transformation,[],[f25])).
% 19.65/2.99  
% 19.65/2.99  fof(f84,plain,(
% 19.65/2.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.65/2.99    inference(cnf_transformation,[],[f37])).
% 19.65/2.99  
% 19.65/2.99  fof(f13,axiom,(
% 19.65/2.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f31,plain,(
% 19.65/2.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.65/2.99    inference(ennf_transformation,[],[f13])).
% 19.65/2.99  
% 19.65/2.99  fof(f55,plain,(
% 19.65/2.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 19.65/2.99    inference(nnf_transformation,[],[f31])).
% 19.65/2.99  
% 19.65/2.99  fof(f78,plain,(
% 19.65/2.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f55])).
% 19.65/2.99  
% 19.65/2.99  fof(f8,axiom,(
% 19.65/2.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f52,plain,(
% 19.65/2.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 19.65/2.99    inference(nnf_transformation,[],[f8])).
% 19.65/2.99  
% 19.65/2.99  fof(f53,plain,(
% 19.65/2.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 19.65/2.99    inference(flattening,[],[f52])).
% 19.65/2.99  
% 19.65/2.99  fof(f70,plain,(
% 19.65/2.99    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 19.65/2.99    inference(cnf_transformation,[],[f53])).
% 19.65/2.99  
% 19.65/2.99  fof(f105,plain,(
% 19.65/2.99    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 19.65/2.99    inference(definition_unfolding,[],[f70,f102,f102])).
% 19.65/2.99  
% 19.65/2.99  fof(f2,axiom,(
% 19.65/2.99    v1_xboole_0(o_0_0_xboole_0)),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f62,plain,(
% 19.65/2.99    v1_xboole_0(o_0_0_xboole_0)),
% 19.65/2.99    inference(cnf_transformation,[],[f2])).
% 19.65/2.99  
% 19.65/2.99  fof(f3,axiom,(
% 19.65/2.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f27,plain,(
% 19.65/2.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 19.65/2.99    inference(ennf_transformation,[],[f3])).
% 19.65/2.99  
% 19.65/2.99  fof(f63,plain,(
% 19.65/2.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f27])).
% 19.65/2.99  
% 19.65/2.99  fof(f16,axiom,(
% 19.65/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f36,plain,(
% 19.65/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.65/2.99    inference(ennf_transformation,[],[f16])).
% 19.65/2.99  
% 19.65/2.99  fof(f83,plain,(
% 19.65/2.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.65/2.99    inference(cnf_transformation,[],[f36])).
% 19.65/2.99  
% 19.65/2.99  fof(f10,axiom,(
% 19.65/2.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f54,plain,(
% 19.65/2.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.65/2.99    inference(nnf_transformation,[],[f10])).
% 19.65/2.99  
% 19.65/2.99  fof(f74,plain,(
% 19.65/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.65/2.99    inference(cnf_transformation,[],[f54])).
% 19.65/2.99  
% 19.65/2.99  fof(f1,axiom,(
% 19.65/2.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f26,plain,(
% 19.65/2.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.65/2.99    inference(ennf_transformation,[],[f1])).
% 19.65/2.99  
% 19.65/2.99  fof(f46,plain,(
% 19.65/2.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.65/2.99    inference(nnf_transformation,[],[f26])).
% 19.65/2.99  
% 19.65/2.99  fof(f47,plain,(
% 19.65/2.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.65/2.99    inference(rectify,[],[f46])).
% 19.65/2.99  
% 19.65/2.99  fof(f48,plain,(
% 19.65/2.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.65/2.99    introduced(choice_axiom,[])).
% 19.65/2.99  
% 19.65/2.99  fof(f49,plain,(
% 19.65/2.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.65/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 19.65/2.99  
% 19.65/2.99  fof(f60,plain,(
% 19.65/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f49])).
% 19.65/2.99  
% 19.65/2.99  fof(f12,axiom,(
% 19.65/2.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f30,plain,(
% 19.65/2.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 19.65/2.99    inference(ennf_transformation,[],[f12])).
% 19.65/2.99  
% 19.65/2.99  fof(f77,plain,(
% 19.65/2.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f30])).
% 19.65/2.99  
% 19.65/2.99  fof(f75,plain,(
% 19.65/2.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f54])).
% 19.65/2.99  
% 19.65/2.99  fof(f96,plain,(
% 19.65/2.99    v1_funct_1(sK3)),
% 19.65/2.99    inference(cnf_transformation,[],[f58])).
% 19.65/2.99  
% 19.65/2.99  fof(f9,axiom,(
% 19.65/2.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f73,plain,(
% 19.65/2.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 19.65/2.99    inference(cnf_transformation,[],[f9])).
% 19.65/2.99  
% 19.65/2.99  fof(f14,axiom,(
% 19.65/2.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f32,plain,(
% 19.65/2.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 19.65/2.99    inference(ennf_transformation,[],[f14])).
% 19.65/2.99  
% 19.65/2.99  fof(f33,plain,(
% 19.65/2.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 19.65/2.99    inference(flattening,[],[f32])).
% 19.65/2.99  
% 19.65/2.99  fof(f80,plain,(
% 19.65/2.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f33])).
% 19.65/2.99  
% 19.65/2.99  fof(f19,axiom,(
% 19.65/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f39,plain,(
% 19.65/2.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.65/2.99    inference(ennf_transformation,[],[f19])).
% 19.65/2.99  
% 19.65/2.99  fof(f86,plain,(
% 19.65/2.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.65/2.99    inference(cnf_transformation,[],[f39])).
% 19.65/2.99  
% 19.65/2.99  fof(f100,plain,(
% 19.65/2.99    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)),
% 19.65/2.99    inference(cnf_transformation,[],[f58])).
% 19.65/2.99  
% 19.65/2.99  fof(f107,plain,(
% 19.65/2.99    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)),
% 19.65/2.99    inference(definition_unfolding,[],[f100,f102,f102])).
% 19.65/2.99  
% 19.65/2.99  fof(f15,axiom,(
% 19.65/2.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f34,plain,(
% 19.65/2.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 19.65/2.99    inference(ennf_transformation,[],[f15])).
% 19.65/2.99  
% 19.65/2.99  fof(f35,plain,(
% 19.65/2.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.65/2.99    inference(flattening,[],[f34])).
% 19.65/2.99  
% 19.65/2.99  fof(f82,plain,(
% 19.65/2.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f35])).
% 19.65/2.99  
% 19.65/2.99  fof(f106,plain,(
% 19.65/2.99    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.65/2.99    inference(definition_unfolding,[],[f82,f102,f102])).
% 19.65/2.99  
% 19.65/2.99  fof(f4,axiom,(
% 19.65/2.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f50,plain,(
% 19.65/2.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.65/2.99    inference(nnf_transformation,[],[f4])).
% 19.65/2.99  
% 19.65/2.99  fof(f51,plain,(
% 19.65/2.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.65/2.99    inference(flattening,[],[f50])).
% 19.65/2.99  
% 19.65/2.99  fof(f66,plain,(
% 19.65/2.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.65/2.99    inference(cnf_transformation,[],[f51])).
% 19.65/2.99  
% 19.65/2.99  fof(f21,axiom,(
% 19.65/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f41,plain,(
% 19.65/2.99    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 19.65/2.99    inference(ennf_transformation,[],[f21])).
% 19.65/2.99  
% 19.65/2.99  fof(f89,plain,(
% 19.65/2.99    ( ! [X2,X0,X1] : (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 19.65/2.99    inference(cnf_transformation,[],[f41])).
% 19.65/2.99  
% 19.65/2.99  fof(f22,axiom,(
% 19.65/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f42,plain,(
% 19.65/2.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.65/2.99    inference(ennf_transformation,[],[f22])).
% 19.65/2.99  
% 19.65/2.99  fof(f43,plain,(
% 19.65/2.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.65/2.99    inference(flattening,[],[f42])).
% 19.65/2.99  
% 19.65/2.99  fof(f56,plain,(
% 19.65/2.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.65/2.99    inference(nnf_transformation,[],[f43])).
% 19.65/2.99  
% 19.65/2.99  fof(f90,plain,(
% 19.65/2.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.65/2.99    inference(cnf_transformation,[],[f56])).
% 19.65/2.99  
% 19.65/2.99  fof(f97,plain,(
% 19.65/2.99    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 19.65/2.99    inference(cnf_transformation,[],[f58])).
% 19.65/2.99  
% 19.65/2.99  fof(f109,plain,(
% 19.65/2.99    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 19.65/2.99    inference(definition_unfolding,[],[f97,f102])).
% 19.65/2.99  
% 19.65/2.99  fof(f99,plain,(
% 19.65/2.99    k1_xboole_0 != sK2),
% 19.65/2.99    inference(cnf_transformation,[],[f58])).
% 19.65/2.99  
% 19.65/2.99  fof(f20,axiom,(
% 19.65/2.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f40,plain,(
% 19.65/2.99    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.65/2.99    inference(ennf_transformation,[],[f20])).
% 19.65/2.99  
% 19.65/2.99  fof(f87,plain,(
% 19.65/2.99    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.65/2.99    inference(cnf_transformation,[],[f40])).
% 19.65/2.99  
% 19.65/2.99  fof(f18,axiom,(
% 19.65/2.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 19.65/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.65/2.99  
% 19.65/2.99  fof(f38,plain,(
% 19.65/2.99    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.65/2.99    inference(ennf_transformation,[],[f18])).
% 19.65/2.99  
% 19.65/2.99  fof(f85,plain,(
% 19.65/2.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.65/2.99    inference(cnf_transformation,[],[f38])).
% 19.65/2.99  
% 19.65/2.99  cnf(c_36,negated_conjecture,
% 19.65/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 19.65/2.99      inference(cnf_transformation,[],[f108]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1447,plain,
% 19.65/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_22,plain,
% 19.65/2.99      ( v4_relat_1(X0,X1)
% 19.65/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 19.65/2.99      inference(cnf_transformation,[],[f84]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1459,plain,
% 19.65/2.99      ( v4_relat_1(X0,X1) = iProver_top
% 19.65/2.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2807,plain,
% 19.65/2.99      ( v4_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1447,c_1459]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_17,plain,
% 19.65/2.99      ( ~ v4_relat_1(X0,X1)
% 19.65/2.99      | r1_tarski(k1_relat_1(X0),X1)
% 19.65/2.99      | ~ v1_relat_1(X0) ),
% 19.65/2.99      inference(cnf_transformation,[],[f78]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1464,plain,
% 19.65/2.99      ( v4_relat_1(X0,X1) != iProver_top
% 19.65/2.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 19.65/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_10,plain,
% 19.65/2.99      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 19.65/2.99      | k2_enumset1(X1,X1,X1,X1) = X0
% 19.65/2.99      | k1_xboole_0 = X0 ),
% 19.65/2.99      inference(cnf_transformation,[],[f105]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1470,plain,
% 19.65/2.99      ( k2_enumset1(X0,X0,X0,X0) = X1
% 19.65/2.99      | k1_xboole_0 = X1
% 19.65/2.99      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3,plain,
% 19.65/2.99      ( v1_xboole_0(o_0_0_xboole_0) ),
% 19.65/2.99      inference(cnf_transformation,[],[f62]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1476,plain,
% 19.65/2.99      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_4,plain,
% 19.65/2.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 19.65/2.99      inference(cnf_transformation,[],[f63]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1475,plain,
% 19.65/2.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1999,plain,
% 19.65/2.99      ( k1_xboole_0 = o_0_0_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1476,c_1475]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_5637,plain,
% 19.65/2.99      ( k2_enumset1(X0,X0,X0,X0) = X1
% 19.65/2.99      | o_0_0_xboole_0 = X1
% 19.65/2.99      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_1470,c_1999]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_5645,plain,
% 19.65/2.99      ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(X1)
% 19.65/2.99      | k1_relat_1(X1) = o_0_0_xboole_0
% 19.65/2.99      | v4_relat_1(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top
% 19.65/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1464,c_5637]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_44291,plain,
% 19.65/2.99      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 19.65/2.99      | k1_relat_1(sK3) = o_0_0_xboole_0
% 19.65/2.99      | v1_relat_1(sK3) != iProver_top ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_2807,c_5645]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_21,plain,
% 19.65/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.65/2.99      | v1_relat_1(X0) ),
% 19.65/2.99      inference(cnf_transformation,[],[f83]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1766,plain,
% 19.65/2.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 19.65/2.99      | v1_relat_1(sK3) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_21]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_44359,plain,
% 19.65/2.99      ( ~ v1_relat_1(sK3)
% 19.65/2.99      | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 19.65/2.99      | k1_relat_1(sK3) = o_0_0_xboole_0 ),
% 19.65/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_44291]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_45733,plain,
% 19.65/2.99      ( k1_relat_1(sK3) = o_0_0_xboole_0
% 19.65/2.99      | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
% 19.65/2.99      inference(global_propositional_subsumption,
% 19.65/2.99                [status(thm)],
% 19.65/2.99                [c_44291,c_36,c_1766,c_44359]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_45734,plain,
% 19.65/2.99      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 19.65/2.99      | k1_relat_1(sK3) = o_0_0_xboole_0 ),
% 19.65/2.99      inference(renaming,[status(thm)],[c_45733]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_13,plain,
% 19.65/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.65/2.99      inference(cnf_transformation,[],[f74]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1467,plain,
% 19.65/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.65/2.99      | r1_tarski(X0,X1) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2004,plain,
% 19.65/2.99      ( r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = iProver_top ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1447,c_1467]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1,plain,
% 19.65/2.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 19.65/2.99      inference(cnf_transformation,[],[f60]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1478,plain,
% 19.65/2.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 19.65/2.99      | r1_tarski(X0,X1) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_15,plain,
% 19.65/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.65/2.99      | ~ r2_hidden(X2,X0)
% 19.65/2.99      | ~ v1_xboole_0(X1) ),
% 19.65/2.99      inference(cnf_transformation,[],[f77]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_12,plain,
% 19.65/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.65/2.99      inference(cnf_transformation,[],[f75]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_258,plain,
% 19.65/2.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.65/2.99      inference(prop_impl,[status(thm)],[c_12]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_259,plain,
% 19.65/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.65/2.99      inference(renaming,[status(thm)],[c_258]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_324,plain,
% 19.65/2.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 19.65/2.99      inference(bin_hyper_res,[status(thm)],[c_15,c_259]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1444,plain,
% 19.65/2.99      ( r2_hidden(X0,X1) != iProver_top
% 19.65/2.99      | r1_tarski(X1,X2) != iProver_top
% 19.65/2.99      | v1_xboole_0(X2) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_13781,plain,
% 19.65/2.99      ( r1_tarski(X0,X1) != iProver_top
% 19.65/2.99      | r1_tarski(X0,X2) = iProver_top
% 19.65/2.99      | v1_xboole_0(X1) != iProver_top ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1478,c_1444]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_13990,plain,
% 19.65/2.99      ( r1_tarski(sK3,X0) = iProver_top
% 19.65/2.99      | v1_xboole_0(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != iProver_top ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_2004,c_13781]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_45748,plain,
% 19.65/2.99      ( k1_relat_1(sK3) = o_0_0_xboole_0
% 19.65/2.99      | r1_tarski(sK3,X0) = iProver_top
% 19.65/2.99      | v1_xboole_0(k2_zfmisc_1(k1_relat_1(sK3),sK2)) != iProver_top ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_45734,c_13990]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_38,negated_conjecture,
% 19.65/2.99      ( v1_funct_1(sK3) ),
% 19.65/2.99      inference(cnf_transformation,[],[f96]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_41,plain,
% 19.65/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_11,plain,
% 19.65/2.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 19.65/2.99      inference(cnf_transformation,[],[f73]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_108,plain,
% 19.65/2.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1767,plain,
% 19.65/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) != iProver_top
% 19.65/2.99      | v1_relat_1(sK3) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_1766]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_19,plain,
% 19.65/2.99      ( ~ v1_relat_1(X0)
% 19.65/2.99      | k1_relat_1(X0) != k1_xboole_0
% 19.65/2.99      | k1_xboole_0 = X0 ),
% 19.65/2.99      inference(cnf_transformation,[],[f80]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1956,plain,
% 19.65/2.99      ( ~ v1_relat_1(sK3)
% 19.65/2.99      | k1_relat_1(sK3) != k1_xboole_0
% 19.65/2.99      | k1_xboole_0 = sK3 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_19]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_657,plain,( X0 = X0 ),theory(equality) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2082,plain,
% 19.65/2.99      ( sK3 = sK3 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_657]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2307,plain,
% 19.65/2.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_13]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2308,plain,
% 19.65/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 19.65/2.99      | r1_tarski(sK3,X0) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_2307]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2737,plain,
% 19.65/2.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_657]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_24,plain,
% 19.65/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.65/2.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 19.65/2.99      inference(cnf_transformation,[],[f86]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1457,plain,
% 19.65/2.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 19.65/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3395,plain,
% 19.65/2.99      ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1447,c_1457]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_34,negated_conjecture,
% 19.65/2.99      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
% 19.65/2.99      inference(cnf_transformation,[],[f107]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3527,plain,
% 19.65/2.99      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_3395,c_34]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_658,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2173,plain,
% 19.65/2.99      ( k1_relat_1(sK3) != X0
% 19.65/2.99      | k1_relat_1(sK3) = k1_xboole_0
% 19.65/2.99      | k1_xboole_0 != X0 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_658]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3599,plain,
% 19.65/2.99      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 19.65/2.99      | k1_relat_1(sK3) = k1_xboole_0
% 19.65/2.99      | k1_xboole_0 != k1_relat_1(sK3) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_2173]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3600,plain,
% 19.65/2.99      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_657]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2387,plain,
% 19.65/2.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_658]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3948,plain,
% 19.65/2.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_2387]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3949,plain,
% 19.65/2.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_3948]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_664,plain,
% 19.65/2.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.65/2.99      theory(equality) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1845,plain,
% 19.65/2.99      ( m1_subset_1(X0,X1)
% 19.65/2.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X2))
% 19.65/2.99      | X1 != k1_zfmisc_1(X2)
% 19.65/2.99      | X0 != k1_xboole_0 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_664]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2736,plain,
% 19.65/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.65/2.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 19.65/2.99      | X0 != k1_xboole_0
% 19.65/2.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_1845]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_4522,plain,
% 19.65/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(X0))
% 19.65/2.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
% 19.65/2.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
% 19.65/2.99      | sK3 != k1_xboole_0 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_2736]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_4523,plain,
% 19.65/2.99      ( k1_zfmisc_1(X0) != k1_zfmisc_1(X0)
% 19.65/2.99      | sK3 != k1_xboole_0
% 19.65/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) = iProver_top
% 19.65/2.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_4522]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_7692,plain,
% 19.65/2.99      ( ~ v1_xboole_0(k1_relat_1(sK3)) | k1_xboole_0 = k1_relat_1(sK3) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_4]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_661,plain,
% 19.65/2.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 19.65/2.99      theory(equality) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1803,plain,
% 19.65/2.99      ( v1_xboole_0(X0)
% 19.65/2.99      | ~ v1_xboole_0(o_0_0_xboole_0)
% 19.65/2.99      | X0 != o_0_0_xboole_0 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_661]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_49828,plain,
% 19.65/2.99      ( v1_xboole_0(k1_relat_1(sK3))
% 19.65/2.99      | ~ v1_xboole_0(o_0_0_xboole_0)
% 19.65/2.99      | k1_relat_1(sK3) != o_0_0_xboole_0 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_1803]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_20,plain,
% 19.65/2.99      ( ~ v1_funct_1(X0)
% 19.65/2.99      | ~ v1_relat_1(X0)
% 19.65/2.99      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 19.65/2.99      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 19.65/2.99      inference(cnf_transformation,[],[f106]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1955,plain,
% 19.65/2.99      ( ~ v1_funct_1(sK3)
% 19.65/2.99      | ~ v1_relat_1(sK3)
% 19.65/2.99      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 19.65/2.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_20]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_61586,plain,
% 19.65/2.99      ( ~ v1_funct_1(sK3)
% 19.65/2.99      | ~ v1_relat_1(sK3)
% 19.65/2.99      | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
% 19.65/2.99      | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK3) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_1955]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_61802,plain,
% 19.65/2.99      ( r1_tarski(sK3,X0) = iProver_top ),
% 19.65/2.99      inference(global_propositional_subsumption,
% 19.65/2.99                [status(thm)],
% 19.65/2.99                [c_45748,c_38,c_36,c_41,c_108,c_3,c_1766,c_1767,c_1956,
% 19.65/2.99                 c_2082,c_2308,c_2737,c_3527,c_3599,c_3600,c_3949,c_4523,
% 19.65/2.99                 c_7692,c_44291,c_49828,c_61586]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1469,plain,
% 19.65/2.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2003,plain,
% 19.65/2.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1469,c_1467]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2341,plain,
% 19.65/2.99      ( r1_tarski(o_0_0_xboole_0,X0) = iProver_top ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_2003,c_1999]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_5,plain,
% 19.65/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 19.65/2.99      inference(cnf_transformation,[],[f66]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1474,plain,
% 19.65/2.99      ( X0 = X1
% 19.65/2.99      | r1_tarski(X1,X0) != iProver_top
% 19.65/2.99      | r1_tarski(X0,X1) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_3513,plain,
% 19.65/2.99      ( o_0_0_xboole_0 = X0
% 19.65/2.99      | r1_tarski(X0,o_0_0_xboole_0) != iProver_top ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_2341,c_1474]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_61820,plain,
% 19.65/2.99      ( sK3 = o_0_0_xboole_0 ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_61802,c_3513]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_26,plain,
% 19.65/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.65/2.99      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
% 19.65/2.99      inference(cnf_transformation,[],[f89]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1455,plain,
% 19.65/2.99      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
% 19.65/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_6875,plain,
% 19.65/2.99      ( k8_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k2_enumset1(sK1,sK1,sK1,sK1))) = k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1447,c_1455]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_33,plain,
% 19.65/2.99      ( ~ v1_funct_2(X0,X1,X2)
% 19.65/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.65/2.99      | k1_relset_1(X1,X2,X0) = X1
% 19.65/2.99      | k1_xboole_0 = X2 ),
% 19.65/2.99      inference(cnf_transformation,[],[f90]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1448,plain,
% 19.65/2.99      ( k1_relset_1(X0,X1,X2) = X0
% 19.65/2.99      | k1_xboole_0 = X1
% 19.65/2.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 19.65/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1921,plain,
% 19.65/2.99      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_enumset1(sK1,sK1,sK1,sK1)
% 19.65/2.99      | sK2 = k1_xboole_0
% 19.65/2.99      | v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) != iProver_top ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1447,c_1448]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_37,negated_conjecture,
% 19.65/2.99      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 19.65/2.99      inference(cnf_transformation,[],[f109]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_40,plain,
% 19.65/2.99      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_35,negated_conjecture,
% 19.65/2.99      ( k1_xboole_0 != sK2 ),
% 19.65/2.99      inference(cnf_transformation,[],[f99]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_103,plain,
% 19.65/2.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 19.65/2.99      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_13]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_109,plain,
% 19.65/2.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_11]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_125,plain,
% 19.65/2.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 19.65/2.99      | k1_xboole_0 = k1_xboole_0 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1801,plain,
% 19.65/2.99      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_658]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1802,plain,
% 19.65/2.99      ( sK2 != k1_xboole_0
% 19.65/2.99      | k1_xboole_0 = sK2
% 19.65/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_1801]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2201,plain,
% 19.65/2.99      ( k1_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 19.65/2.99      inference(global_propositional_subsumption,
% 19.65/2.99                [status(thm)],
% 19.65/2.99                [c_1921,c_40,c_35,c_103,c_109,c_125,c_1802]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_6885,plain,
% 19.65/2.99      ( k8_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k2_enumset1(sK1,sK1,sK1,sK1))) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 19.65/2.99      inference(light_normalisation,[status(thm)],[c_6875,c_2201]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_25,plain,
% 19.65/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.65/2.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 19.65/2.99      inference(cnf_transformation,[],[f87]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1456,plain,
% 19.65/2.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 19.65/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_4133,plain,
% 19.65/2.99      ( k8_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,X0) = k10_relat_1(sK3,X0) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_1447,c_1456]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_7479,plain,
% 19.65/2.99      ( k10_relat_1(sK3,k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3,k2_enumset1(sK1,sK1,sK1,sK1))) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_6885,c_4133]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_87462,plain,
% 19.65/2.99      ( k10_relat_1(o_0_0_xboole_0,k7_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,o_0_0_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_61820,c_7479]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2208,plain,
% 19.65/2.99      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 19.65/2.99      inference(demodulation,[status(thm)],[c_1999,c_1469]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_4134,plain,
% 19.65/2.99      ( k8_relset_1(X0,X1,o_0_0_xboole_0,X2) = k10_relat_1(o_0_0_xboole_0,X2) ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_2208,c_1456]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_23,plain,
% 19.65/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.65/2.99      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 19.65/2.99      inference(cnf_transformation,[],[f85]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1458,plain,
% 19.65/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.65/2.99      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_5454,plain,
% 19.65/2.99      ( m1_subset_1(k10_relat_1(o_0_0_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top
% 19.65/2.99      | m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_4134,c_1458]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_10144,plain,
% 19.65/2.99      ( m1_subset_1(k10_relat_1(o_0_0_xboole_0,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 19.65/2.99      inference(forward_subsumption_resolution,
% 19.65/2.99                [status(thm)],
% 19.65/2.99                [c_5454,c_2208]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_89628,plain,
% 19.65/2.99      ( m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(X0)) = iProver_top ),
% 19.65/2.99      inference(superposition,[status(thm)],[c_87462,c_10144]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_89790,plain,
% 19.65/2.99      ( m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_89628]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_12606,plain,
% 19.65/2.99      ( ~ r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)),k2_enumset1(sK1,sK1,sK1,sK1))
% 19.65/2.99      | ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0)
% 19.65/2.99      | ~ v1_xboole_0(X0) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_324]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_12617,plain,
% 19.65/2.99      ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 19.65/2.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) != iProver_top
% 19.65/2.99      | v1_xboole_0(X0) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_12606]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_12619,plain,
% 19.65/2.99      ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 19.65/2.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) != iProver_top
% 19.65/2.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_12617]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_6236,plain,
% 19.65/2.99      ( ~ m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(X0))
% 19.65/2.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_13]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_6237,plain,
% 19.65/2.99      ( m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(X0)) != iProver_top
% 19.65/2.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_6236]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_6239,plain,
% 19.65/2.99      ( m1_subset_1(k2_enumset1(sK1,sK1,sK1,sK1),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 19.65/2.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) = iProver_top ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_6237]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_5585,plain,
% 19.65/2.99      ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)),k2_enumset1(sK1,sK1,sK1,sK1))
% 19.65/2.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_1]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_5589,plain,
% 19.65/2.99      ( r2_hidden(sK0(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
% 19.65/2.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_5585]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2448,plain,
% 19.65/2.99      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK3))
% 19.65/2.99      | ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0))
% 19.65/2.99      | k2_enumset1(X0,X0,X0,X0) = k1_relat_1(sK3) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_5]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_4262,plain,
% 19.65/2.99      ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3))
% 19.65/2.99      | ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
% 19.65/2.99      | k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_2448]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_4263,plain,
% 19.65/2.99      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 19.65/2.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top
% 19.65/2.99      | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_4262]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1953,plain,
% 19.65/2.99      ( ~ v4_relat_1(sK3,X0)
% 19.65/2.99      | r1_tarski(k1_relat_1(sK3),X0)
% 19.65/2.99      | ~ v1_relat_1(sK3) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_17]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2282,plain,
% 19.65/2.99      ( ~ v4_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))
% 19.65/2.99      | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
% 19.65/2.99      | ~ v1_relat_1(sK3) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_1953]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_2283,plain,
% 19.65/2.99      ( v4_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 19.65/2.99      | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
% 19.65/2.99      | v1_relat_1(sK3) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_2282]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1807,plain,
% 19.65/2.99      ( X0 != o_0_0_xboole_0
% 19.65/2.99      | v1_xboole_0(X0) = iProver_top
% 19.65/2.99      | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_1803]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1809,plain,
% 19.65/2.99      ( k1_xboole_0 != o_0_0_xboole_0
% 19.65/2.99      | v1_xboole_0(k1_xboole_0) = iProver_top
% 19.65/2.99      | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_1807]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1804,plain,
% 19.65/2.99      ( ~ v1_xboole_0(o_0_0_xboole_0) | k1_xboole_0 = o_0_0_xboole_0 ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_4]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1777,plain,
% 19.65/2.99      ( v4_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1))
% 19.65/2.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 19.65/2.99      inference(instantiation,[status(thm)],[c_22]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_1778,plain,
% 19.65/2.99      ( v4_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top
% 19.65/2.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) != iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_1777]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(c_130,plain,
% 19.65/2.99      ( v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 19.65/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.65/2.99  
% 19.65/2.99  cnf(contradiction,plain,
% 19.65/2.99      ( $false ),
% 19.65/2.99      inference(minisat,
% 19.65/2.99                [status(thm)],
% 19.65/2.99                [c_89790,c_61586,c_12619,c_6239,c_5589,c_4263,c_3527,
% 19.65/2.99                 c_2283,c_1809,c_1804,c_1778,c_1767,c_1766,c_130,c_3,
% 19.65/2.99                 c_41,c_36,c_38]) ).
% 19.65/2.99  
% 19.65/2.99  
% 19.65/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.65/2.99  
% 19.65/2.99  ------                               Statistics
% 19.65/2.99  
% 19.65/2.99  ------ Selected
% 19.65/2.99  
% 19.65/2.99  total_time:                             2.385
% 19.65/2.99  
%------------------------------------------------------------------------------
