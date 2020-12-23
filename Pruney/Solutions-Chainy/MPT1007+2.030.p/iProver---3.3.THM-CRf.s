%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:48 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 295 expanded)
%              Number of clauses        :   66 (  85 expanded)
%              Number of leaves         :   18 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  311 ( 831 expanded)
%              Number of equality atoms :  106 ( 240 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f45])).

fof(f52,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f50])).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f88,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f81,f84])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f80,f84])).

fof(f79,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f85,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f56,f84])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f84])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1372,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1356,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1361,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2653,plain,
    ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1356,c_1361])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_379,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_383,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_379,c_29,c_27,c_26])).

cnf(c_1351,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_2889,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2653,c_1351])).

cnf(c_3078,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),k2_relat_1(sK4)) = iProver_top
    | v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_2889])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1663,plain,
    ( ~ v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1664,plain,
    ( v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1663])).

cnf(c_3805,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3078,c_1664])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1362,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1850,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_1362])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1368,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2783,plain,
    ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1850,c_1368])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_18,c_9])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_18,c_16,c_9])).

cnf(c_1353,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_2105,plain,
    ( k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) = sK4 ),
    inference(superposition,[status(thm)],[c_1356,c_1353])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1367,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2005,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_1850,c_1367])).

cnf(c_2328,plain,
    ( k9_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2105,c_2005])).

cnf(c_2989,plain,
    ( k11_relat_1(sK4,sK2) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2783,c_2328])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1366,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_14,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_14])).

cnf(c_354,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_16])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_1352,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r2_hidden(X3,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X3),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_1657,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_1352])).

cnf(c_30,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1739,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1657,c_30])).

cnf(c_1740,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_1739])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1357,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1747,plain,
    ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1740,c_1357])).

cnf(c_2855,plain,
    ( k11_relat_1(sK4,sK2) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_1747])).

cnf(c_32,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1545,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1546,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1545])).

cnf(c_3002,plain,
    ( k11_relat_1(sK4,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2855,c_32,c_1546])).

cnf(c_3164,plain,
    ( k2_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2989,c_3002])).

cnf(c_3809,plain,
    ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3805,c_3164])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_319,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_320,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_1354,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_3811,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3809,c_1354])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:12:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.69/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.03  
% 2.69/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.69/1.03  
% 2.69/1.03  ------  iProver source info
% 2.69/1.03  
% 2.69/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.69/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.69/1.03  git: non_committed_changes: false
% 2.69/1.03  git: last_make_outside_of_git: false
% 2.69/1.03  
% 2.69/1.03  ------ 
% 2.69/1.03  
% 2.69/1.03  ------ Input Options
% 2.69/1.03  
% 2.69/1.03  --out_options                           all
% 2.69/1.03  --tptp_safe_out                         true
% 2.69/1.03  --problem_path                          ""
% 2.69/1.03  --include_path                          ""
% 2.69/1.03  --clausifier                            res/vclausify_rel
% 2.69/1.03  --clausifier_options                    --mode clausify
% 2.69/1.03  --stdin                                 false
% 2.69/1.03  --stats_out                             all
% 2.69/1.03  
% 2.69/1.03  ------ General Options
% 2.69/1.03  
% 2.69/1.03  --fof                                   false
% 2.69/1.03  --time_out_real                         305.
% 2.69/1.03  --time_out_virtual                      -1.
% 2.69/1.03  --symbol_type_check                     false
% 2.69/1.03  --clausify_out                          false
% 2.69/1.03  --sig_cnt_out                           false
% 2.69/1.03  --trig_cnt_out                          false
% 2.69/1.03  --trig_cnt_out_tolerance                1.
% 2.69/1.03  --trig_cnt_out_sk_spl                   false
% 2.69/1.03  --abstr_cl_out                          false
% 2.69/1.03  
% 2.69/1.03  ------ Global Options
% 2.69/1.03  
% 2.69/1.03  --schedule                              default
% 2.69/1.03  --add_important_lit                     false
% 2.69/1.03  --prop_solver_per_cl                    1000
% 2.69/1.03  --min_unsat_core                        false
% 2.69/1.03  --soft_assumptions                      false
% 2.69/1.03  --soft_lemma_size                       3
% 2.69/1.03  --prop_impl_unit_size                   0
% 2.69/1.03  --prop_impl_unit                        []
% 2.69/1.03  --share_sel_clauses                     true
% 2.69/1.03  --reset_solvers                         false
% 2.69/1.03  --bc_imp_inh                            [conj_cone]
% 2.69/1.03  --conj_cone_tolerance                   3.
% 2.69/1.03  --extra_neg_conj                        none
% 2.69/1.03  --large_theory_mode                     true
% 2.69/1.03  --prolific_symb_bound                   200
% 2.69/1.03  --lt_threshold                          2000
% 2.69/1.03  --clause_weak_htbl                      true
% 2.69/1.03  --gc_record_bc_elim                     false
% 2.69/1.03  
% 2.69/1.03  ------ Preprocessing Options
% 2.69/1.03  
% 2.69/1.03  --preprocessing_flag                    true
% 2.69/1.03  --time_out_prep_mult                    0.1
% 2.69/1.03  --splitting_mode                        input
% 2.69/1.03  --splitting_grd                         true
% 2.69/1.03  --splitting_cvd                         false
% 2.69/1.03  --splitting_cvd_svl                     false
% 2.69/1.03  --splitting_nvd                         32
% 2.69/1.03  --sub_typing                            true
% 2.69/1.03  --prep_gs_sim                           true
% 2.69/1.03  --prep_unflatten                        true
% 2.69/1.03  --prep_res_sim                          true
% 2.69/1.03  --prep_upred                            true
% 2.69/1.03  --prep_sem_filter                       exhaustive
% 2.69/1.03  --prep_sem_filter_out                   false
% 2.69/1.03  --pred_elim                             true
% 2.69/1.03  --res_sim_input                         true
% 2.69/1.03  --eq_ax_congr_red                       true
% 2.69/1.03  --pure_diseq_elim                       true
% 2.69/1.03  --brand_transform                       false
% 2.69/1.03  --non_eq_to_eq                          false
% 2.69/1.03  --prep_def_merge                        true
% 2.69/1.03  --prep_def_merge_prop_impl              false
% 2.69/1.03  --prep_def_merge_mbd                    true
% 2.69/1.03  --prep_def_merge_tr_red                 false
% 2.69/1.03  --prep_def_merge_tr_cl                  false
% 2.69/1.03  --smt_preprocessing                     true
% 2.69/1.03  --smt_ac_axioms                         fast
% 2.69/1.03  --preprocessed_out                      false
% 2.69/1.03  --preprocessed_stats                    false
% 2.69/1.03  
% 2.69/1.03  ------ Abstraction refinement Options
% 2.69/1.03  
% 2.69/1.03  --abstr_ref                             []
% 2.69/1.03  --abstr_ref_prep                        false
% 2.69/1.03  --abstr_ref_until_sat                   false
% 2.69/1.03  --abstr_ref_sig_restrict                funpre
% 2.69/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.03  --abstr_ref_under                       []
% 2.69/1.03  
% 2.69/1.03  ------ SAT Options
% 2.69/1.03  
% 2.69/1.03  --sat_mode                              false
% 2.69/1.03  --sat_fm_restart_options                ""
% 2.69/1.03  --sat_gr_def                            false
% 2.69/1.03  --sat_epr_types                         true
% 2.69/1.03  --sat_non_cyclic_types                  false
% 2.69/1.03  --sat_finite_models                     false
% 2.69/1.03  --sat_fm_lemmas                         false
% 2.69/1.03  --sat_fm_prep                           false
% 2.69/1.03  --sat_fm_uc_incr                        true
% 2.69/1.03  --sat_out_model                         small
% 2.69/1.03  --sat_out_clauses                       false
% 2.69/1.03  
% 2.69/1.03  ------ QBF Options
% 2.69/1.03  
% 2.69/1.03  --qbf_mode                              false
% 2.69/1.03  --qbf_elim_univ                         false
% 2.69/1.03  --qbf_dom_inst                          none
% 2.69/1.03  --qbf_dom_pre_inst                      false
% 2.69/1.03  --qbf_sk_in                             false
% 2.69/1.03  --qbf_pred_elim                         true
% 2.69/1.03  --qbf_split                             512
% 2.69/1.03  
% 2.69/1.03  ------ BMC1 Options
% 2.69/1.03  
% 2.69/1.03  --bmc1_incremental                      false
% 2.69/1.03  --bmc1_axioms                           reachable_all
% 2.69/1.03  --bmc1_min_bound                        0
% 2.69/1.03  --bmc1_max_bound                        -1
% 2.69/1.03  --bmc1_max_bound_default                -1
% 2.69/1.03  --bmc1_symbol_reachability              true
% 2.69/1.03  --bmc1_property_lemmas                  false
% 2.69/1.03  --bmc1_k_induction                      false
% 2.69/1.03  --bmc1_non_equiv_states                 false
% 2.69/1.03  --bmc1_deadlock                         false
% 2.69/1.03  --bmc1_ucm                              false
% 2.69/1.03  --bmc1_add_unsat_core                   none
% 2.69/1.03  --bmc1_unsat_core_children              false
% 2.69/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.03  --bmc1_out_stat                         full
% 2.69/1.03  --bmc1_ground_init                      false
% 2.69/1.03  --bmc1_pre_inst_next_state              false
% 2.69/1.03  --bmc1_pre_inst_state                   false
% 2.69/1.03  --bmc1_pre_inst_reach_state             false
% 2.69/1.03  --bmc1_out_unsat_core                   false
% 2.69/1.03  --bmc1_aig_witness_out                  false
% 2.69/1.03  --bmc1_verbose                          false
% 2.69/1.03  --bmc1_dump_clauses_tptp                false
% 2.69/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.03  --bmc1_dump_file                        -
% 2.69/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.03  --bmc1_ucm_extend_mode                  1
% 2.69/1.03  --bmc1_ucm_init_mode                    2
% 2.69/1.03  --bmc1_ucm_cone_mode                    none
% 2.69/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.03  --bmc1_ucm_relax_model                  4
% 2.69/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.03  --bmc1_ucm_layered_model                none
% 2.69/1.03  --bmc1_ucm_max_lemma_size               10
% 2.69/1.03  
% 2.69/1.03  ------ AIG Options
% 2.69/1.03  
% 2.69/1.03  --aig_mode                              false
% 2.69/1.03  
% 2.69/1.03  ------ Instantiation Options
% 2.69/1.03  
% 2.69/1.03  --instantiation_flag                    true
% 2.69/1.03  --inst_sos_flag                         false
% 2.69/1.03  --inst_sos_phase                        true
% 2.69/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.03  --inst_lit_sel_side                     num_symb
% 2.69/1.03  --inst_solver_per_active                1400
% 2.69/1.03  --inst_solver_calls_frac                1.
% 2.69/1.03  --inst_passive_queue_type               priority_queues
% 2.69/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.03  --inst_passive_queues_freq              [25;2]
% 2.69/1.03  --inst_dismatching                      true
% 2.69/1.03  --inst_eager_unprocessed_to_passive     true
% 2.69/1.03  --inst_prop_sim_given                   true
% 2.69/1.03  --inst_prop_sim_new                     false
% 2.69/1.03  --inst_subs_new                         false
% 2.69/1.03  --inst_eq_res_simp                      false
% 2.69/1.03  --inst_subs_given                       false
% 2.69/1.03  --inst_orphan_elimination               true
% 2.69/1.03  --inst_learning_loop_flag               true
% 2.69/1.03  --inst_learning_start                   3000
% 2.69/1.03  --inst_learning_factor                  2
% 2.69/1.03  --inst_start_prop_sim_after_learn       3
% 2.69/1.03  --inst_sel_renew                        solver
% 2.69/1.03  --inst_lit_activity_flag                true
% 2.69/1.03  --inst_restr_to_given                   false
% 2.69/1.03  --inst_activity_threshold               500
% 2.69/1.03  --inst_out_proof                        true
% 2.69/1.03  
% 2.69/1.03  ------ Resolution Options
% 2.69/1.03  
% 2.69/1.03  --resolution_flag                       true
% 2.69/1.03  --res_lit_sel                           adaptive
% 2.69/1.03  --res_lit_sel_side                      none
% 2.69/1.03  --res_ordering                          kbo
% 2.69/1.03  --res_to_prop_solver                    active
% 2.69/1.03  --res_prop_simpl_new                    false
% 2.69/1.03  --res_prop_simpl_given                  true
% 2.69/1.03  --res_passive_queue_type                priority_queues
% 2.69/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.03  --res_passive_queues_freq               [15;5]
% 2.69/1.03  --res_forward_subs                      full
% 2.69/1.03  --res_backward_subs                     full
% 2.69/1.03  --res_forward_subs_resolution           true
% 2.69/1.03  --res_backward_subs_resolution          true
% 2.69/1.03  --res_orphan_elimination                true
% 2.69/1.03  --res_time_limit                        2.
% 2.69/1.03  --res_out_proof                         true
% 2.69/1.03  
% 2.69/1.03  ------ Superposition Options
% 2.69/1.03  
% 2.69/1.03  --superposition_flag                    true
% 2.69/1.03  --sup_passive_queue_type                priority_queues
% 2.69/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.03  --demod_completeness_check              fast
% 2.69/1.03  --demod_use_ground                      true
% 2.69/1.03  --sup_to_prop_solver                    passive
% 2.69/1.03  --sup_prop_simpl_new                    true
% 2.69/1.03  --sup_prop_simpl_given                  true
% 2.69/1.03  --sup_fun_splitting                     false
% 2.69/1.03  --sup_smt_interval                      50000
% 2.69/1.03  
% 2.69/1.03  ------ Superposition Simplification Setup
% 2.69/1.03  
% 2.69/1.03  --sup_indices_passive                   []
% 2.69/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.03  --sup_full_bw                           [BwDemod]
% 2.69/1.03  --sup_immed_triv                        [TrivRules]
% 2.69/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.03  --sup_immed_bw_main                     []
% 2.69/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.03  
% 2.69/1.03  ------ Combination Options
% 2.69/1.03  
% 2.69/1.03  --comb_res_mult                         3
% 2.69/1.03  --comb_sup_mult                         2
% 2.69/1.03  --comb_inst_mult                        10
% 2.69/1.03  
% 2.69/1.03  ------ Debug Options
% 2.69/1.03  
% 2.69/1.03  --dbg_backtrace                         false
% 2.69/1.03  --dbg_dump_prop_clauses                 false
% 2.69/1.03  --dbg_dump_prop_clauses_file            -
% 2.69/1.03  --dbg_out_stat                          false
% 2.69/1.03  ------ Parsing...
% 2.69/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.69/1.03  
% 2.69/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.69/1.03  
% 2.69/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.69/1.03  
% 2.69/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.69/1.03  ------ Proving...
% 2.69/1.03  ------ Problem Properties 
% 2.69/1.03  
% 2.69/1.03  
% 2.69/1.03  clauses                                 26
% 2.69/1.03  conjectures                             4
% 2.69/1.03  EPR                                     3
% 2.69/1.03  Horn                                    24
% 2.69/1.03  unary                                   12
% 2.69/1.03  binary                                  8
% 2.69/1.03  lits                                    47
% 2.69/1.03  lits eq                                 15
% 2.69/1.03  fd_pure                                 0
% 2.69/1.03  fd_pseudo                               0
% 2.69/1.03  fd_cond                                 2
% 2.69/1.03  fd_pseudo_cond                          0
% 2.69/1.03  AC symbols                              0
% 2.69/1.03  
% 2.69/1.03  ------ Schedule dynamic 5 is on 
% 2.69/1.03  
% 2.69/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.69/1.03  
% 2.69/1.03  
% 2.69/1.03  ------ 
% 2.69/1.03  Current options:
% 2.69/1.03  ------ 
% 2.69/1.03  
% 2.69/1.03  ------ Input Options
% 2.69/1.03  
% 2.69/1.03  --out_options                           all
% 2.69/1.03  --tptp_safe_out                         true
% 2.69/1.03  --problem_path                          ""
% 2.69/1.03  --include_path                          ""
% 2.69/1.03  --clausifier                            res/vclausify_rel
% 2.69/1.03  --clausifier_options                    --mode clausify
% 2.69/1.03  --stdin                                 false
% 2.69/1.03  --stats_out                             all
% 2.69/1.03  
% 2.69/1.03  ------ General Options
% 2.69/1.03  
% 2.69/1.03  --fof                                   false
% 2.69/1.03  --time_out_real                         305.
% 2.69/1.03  --time_out_virtual                      -1.
% 2.69/1.03  --symbol_type_check                     false
% 2.69/1.03  --clausify_out                          false
% 2.69/1.03  --sig_cnt_out                           false
% 2.69/1.03  --trig_cnt_out                          false
% 2.69/1.03  --trig_cnt_out_tolerance                1.
% 2.69/1.03  --trig_cnt_out_sk_spl                   false
% 2.69/1.03  --abstr_cl_out                          false
% 2.69/1.03  
% 2.69/1.03  ------ Global Options
% 2.69/1.03  
% 2.69/1.03  --schedule                              default
% 2.69/1.03  --add_important_lit                     false
% 2.69/1.03  --prop_solver_per_cl                    1000
% 2.69/1.03  --min_unsat_core                        false
% 2.69/1.03  --soft_assumptions                      false
% 2.69/1.03  --soft_lemma_size                       3
% 2.69/1.03  --prop_impl_unit_size                   0
% 2.69/1.03  --prop_impl_unit                        []
% 2.69/1.03  --share_sel_clauses                     true
% 2.69/1.03  --reset_solvers                         false
% 2.69/1.03  --bc_imp_inh                            [conj_cone]
% 2.69/1.03  --conj_cone_tolerance                   3.
% 2.69/1.03  --extra_neg_conj                        none
% 2.69/1.03  --large_theory_mode                     true
% 2.69/1.03  --prolific_symb_bound                   200
% 2.69/1.03  --lt_threshold                          2000
% 2.69/1.03  --clause_weak_htbl                      true
% 2.69/1.03  --gc_record_bc_elim                     false
% 2.69/1.03  
% 2.69/1.03  ------ Preprocessing Options
% 2.69/1.03  
% 2.69/1.03  --preprocessing_flag                    true
% 2.69/1.03  --time_out_prep_mult                    0.1
% 2.69/1.03  --splitting_mode                        input
% 2.69/1.03  --splitting_grd                         true
% 2.69/1.03  --splitting_cvd                         false
% 2.69/1.03  --splitting_cvd_svl                     false
% 2.69/1.03  --splitting_nvd                         32
% 2.69/1.03  --sub_typing                            true
% 2.69/1.03  --prep_gs_sim                           true
% 2.69/1.03  --prep_unflatten                        true
% 2.69/1.03  --prep_res_sim                          true
% 2.69/1.03  --prep_upred                            true
% 2.69/1.03  --prep_sem_filter                       exhaustive
% 2.69/1.03  --prep_sem_filter_out                   false
% 2.69/1.03  --pred_elim                             true
% 2.69/1.03  --res_sim_input                         true
% 2.69/1.03  --eq_ax_congr_red                       true
% 2.69/1.03  --pure_diseq_elim                       true
% 2.69/1.03  --brand_transform                       false
% 2.69/1.03  --non_eq_to_eq                          false
% 2.69/1.03  --prep_def_merge                        true
% 2.69/1.03  --prep_def_merge_prop_impl              false
% 2.69/1.03  --prep_def_merge_mbd                    true
% 2.69/1.03  --prep_def_merge_tr_red                 false
% 2.69/1.03  --prep_def_merge_tr_cl                  false
% 2.69/1.03  --smt_preprocessing                     true
% 2.69/1.03  --smt_ac_axioms                         fast
% 2.69/1.03  --preprocessed_out                      false
% 2.69/1.03  --preprocessed_stats                    false
% 2.69/1.03  
% 2.69/1.03  ------ Abstraction refinement Options
% 2.69/1.03  
% 2.69/1.03  --abstr_ref                             []
% 2.69/1.03  --abstr_ref_prep                        false
% 2.69/1.03  --abstr_ref_until_sat                   false
% 2.69/1.03  --abstr_ref_sig_restrict                funpre
% 2.69/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.69/1.03  --abstr_ref_under                       []
% 2.69/1.03  
% 2.69/1.03  ------ SAT Options
% 2.69/1.03  
% 2.69/1.03  --sat_mode                              false
% 2.69/1.03  --sat_fm_restart_options                ""
% 2.69/1.03  --sat_gr_def                            false
% 2.69/1.03  --sat_epr_types                         true
% 2.69/1.03  --sat_non_cyclic_types                  false
% 2.69/1.03  --sat_finite_models                     false
% 2.69/1.03  --sat_fm_lemmas                         false
% 2.69/1.03  --sat_fm_prep                           false
% 2.69/1.03  --sat_fm_uc_incr                        true
% 2.69/1.03  --sat_out_model                         small
% 2.69/1.03  --sat_out_clauses                       false
% 2.69/1.03  
% 2.69/1.03  ------ QBF Options
% 2.69/1.03  
% 2.69/1.03  --qbf_mode                              false
% 2.69/1.03  --qbf_elim_univ                         false
% 2.69/1.03  --qbf_dom_inst                          none
% 2.69/1.03  --qbf_dom_pre_inst                      false
% 2.69/1.03  --qbf_sk_in                             false
% 2.69/1.03  --qbf_pred_elim                         true
% 2.69/1.03  --qbf_split                             512
% 2.69/1.03  
% 2.69/1.03  ------ BMC1 Options
% 2.69/1.03  
% 2.69/1.03  --bmc1_incremental                      false
% 2.69/1.03  --bmc1_axioms                           reachable_all
% 2.69/1.03  --bmc1_min_bound                        0
% 2.69/1.03  --bmc1_max_bound                        -1
% 2.69/1.03  --bmc1_max_bound_default                -1
% 2.69/1.03  --bmc1_symbol_reachability              true
% 2.69/1.03  --bmc1_property_lemmas                  false
% 2.69/1.03  --bmc1_k_induction                      false
% 2.69/1.03  --bmc1_non_equiv_states                 false
% 2.69/1.03  --bmc1_deadlock                         false
% 2.69/1.03  --bmc1_ucm                              false
% 2.69/1.03  --bmc1_add_unsat_core                   none
% 2.69/1.03  --bmc1_unsat_core_children              false
% 2.69/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.69/1.03  --bmc1_out_stat                         full
% 2.69/1.03  --bmc1_ground_init                      false
% 2.69/1.03  --bmc1_pre_inst_next_state              false
% 2.69/1.03  --bmc1_pre_inst_state                   false
% 2.69/1.03  --bmc1_pre_inst_reach_state             false
% 2.69/1.03  --bmc1_out_unsat_core                   false
% 2.69/1.03  --bmc1_aig_witness_out                  false
% 2.69/1.03  --bmc1_verbose                          false
% 2.69/1.03  --bmc1_dump_clauses_tptp                false
% 2.69/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.69/1.03  --bmc1_dump_file                        -
% 2.69/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.69/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.69/1.03  --bmc1_ucm_extend_mode                  1
% 2.69/1.03  --bmc1_ucm_init_mode                    2
% 2.69/1.03  --bmc1_ucm_cone_mode                    none
% 2.69/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.69/1.03  --bmc1_ucm_relax_model                  4
% 2.69/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.69/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.69/1.03  --bmc1_ucm_layered_model                none
% 2.69/1.03  --bmc1_ucm_max_lemma_size               10
% 2.69/1.03  
% 2.69/1.03  ------ AIG Options
% 2.69/1.03  
% 2.69/1.03  --aig_mode                              false
% 2.69/1.03  
% 2.69/1.03  ------ Instantiation Options
% 2.69/1.03  
% 2.69/1.03  --instantiation_flag                    true
% 2.69/1.03  --inst_sos_flag                         false
% 2.69/1.03  --inst_sos_phase                        true
% 2.69/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.69/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.69/1.03  --inst_lit_sel_side                     none
% 2.69/1.03  --inst_solver_per_active                1400
% 2.69/1.03  --inst_solver_calls_frac                1.
% 2.69/1.03  --inst_passive_queue_type               priority_queues
% 2.69/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.69/1.03  --inst_passive_queues_freq              [25;2]
% 2.69/1.03  --inst_dismatching                      true
% 2.69/1.03  --inst_eager_unprocessed_to_passive     true
% 2.69/1.03  --inst_prop_sim_given                   true
% 2.69/1.03  --inst_prop_sim_new                     false
% 2.69/1.03  --inst_subs_new                         false
% 2.69/1.03  --inst_eq_res_simp                      false
% 2.69/1.03  --inst_subs_given                       false
% 2.69/1.03  --inst_orphan_elimination               true
% 2.69/1.03  --inst_learning_loop_flag               true
% 2.69/1.03  --inst_learning_start                   3000
% 2.69/1.03  --inst_learning_factor                  2
% 2.69/1.03  --inst_start_prop_sim_after_learn       3
% 2.69/1.03  --inst_sel_renew                        solver
% 2.69/1.03  --inst_lit_activity_flag                true
% 2.69/1.03  --inst_restr_to_given                   false
% 2.69/1.03  --inst_activity_threshold               500
% 2.69/1.03  --inst_out_proof                        true
% 2.69/1.03  
% 2.69/1.03  ------ Resolution Options
% 2.69/1.03  
% 2.69/1.03  --resolution_flag                       false
% 2.69/1.03  --res_lit_sel                           adaptive
% 2.69/1.03  --res_lit_sel_side                      none
% 2.69/1.03  --res_ordering                          kbo
% 2.69/1.03  --res_to_prop_solver                    active
% 2.69/1.03  --res_prop_simpl_new                    false
% 2.69/1.03  --res_prop_simpl_given                  true
% 2.69/1.03  --res_passive_queue_type                priority_queues
% 2.69/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.69/1.03  --res_passive_queues_freq               [15;5]
% 2.69/1.03  --res_forward_subs                      full
% 2.69/1.03  --res_backward_subs                     full
% 2.69/1.03  --res_forward_subs_resolution           true
% 2.69/1.03  --res_backward_subs_resolution          true
% 2.69/1.03  --res_orphan_elimination                true
% 2.69/1.03  --res_time_limit                        2.
% 2.69/1.03  --res_out_proof                         true
% 2.69/1.03  
% 2.69/1.03  ------ Superposition Options
% 2.69/1.03  
% 2.69/1.03  --superposition_flag                    true
% 2.69/1.03  --sup_passive_queue_type                priority_queues
% 2.69/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.69/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.69/1.03  --demod_completeness_check              fast
% 2.69/1.03  --demod_use_ground                      true
% 2.69/1.03  --sup_to_prop_solver                    passive
% 2.69/1.03  --sup_prop_simpl_new                    true
% 2.69/1.03  --sup_prop_simpl_given                  true
% 2.69/1.03  --sup_fun_splitting                     false
% 2.69/1.03  --sup_smt_interval                      50000
% 2.69/1.03  
% 2.69/1.03  ------ Superposition Simplification Setup
% 2.69/1.03  
% 2.69/1.03  --sup_indices_passive                   []
% 2.69/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.69/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.69/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.03  --sup_full_bw                           [BwDemod]
% 2.69/1.03  --sup_immed_triv                        [TrivRules]
% 2.69/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.69/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.03  --sup_immed_bw_main                     []
% 2.69/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.69/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.69/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.69/1.03  
% 2.69/1.03  ------ Combination Options
% 2.69/1.03  
% 2.69/1.03  --comb_res_mult                         3
% 2.69/1.03  --comb_sup_mult                         2
% 2.69/1.03  --comb_inst_mult                        10
% 2.69/1.03  
% 2.69/1.03  ------ Debug Options
% 2.69/1.03  
% 2.69/1.03  --dbg_backtrace                         false
% 2.69/1.03  --dbg_dump_prop_clauses                 false
% 2.69/1.03  --dbg_dump_prop_clauses_file            -
% 2.69/1.03  --dbg_out_stat                          false
% 2.69/1.03  
% 2.69/1.03  
% 2.69/1.03  
% 2.69/1.03  
% 2.69/1.03  ------ Proving...
% 2.69/1.03  
% 2.69/1.03  
% 2.69/1.03  % SZS status Theorem for theBenchmark.p
% 2.69/1.03  
% 2.69/1.03   Resolution empty clause
% 2.69/1.03  
% 2.69/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.69/1.03  
% 2.69/1.03  fof(f1,axiom,(
% 2.69/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f23,plain,(
% 2.69/1.03    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 2.69/1.03    inference(unused_predicate_definition_removal,[],[f1])).
% 2.69/1.03  
% 2.69/1.03  fof(f24,plain,(
% 2.69/1.03    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 2.69/1.03    inference(ennf_transformation,[],[f23])).
% 2.69/1.03  
% 2.69/1.03  fof(f45,plain,(
% 2.69/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.69/1.03    introduced(choice_axiom,[])).
% 2.69/1.03  
% 2.69/1.03  fof(f46,plain,(
% 2.69/1.03    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0))),
% 2.69/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f45])).
% 2.69/1.03  
% 2.69/1.03  fof(f52,plain,(
% 2.69/1.03    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.69/1.03    inference(cnf_transformation,[],[f46])).
% 2.69/1.03  
% 2.69/1.03  fof(f21,conjecture,(
% 2.69/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f22,negated_conjecture,(
% 2.69/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.69/1.03    inference(negated_conjecture,[],[f21])).
% 2.69/1.03  
% 2.69/1.03  fof(f43,plain,(
% 2.69/1.03    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.69/1.03    inference(ennf_transformation,[],[f22])).
% 2.69/1.03  
% 2.69/1.03  fof(f44,plain,(
% 2.69/1.03    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.69/1.03    inference(flattening,[],[f43])).
% 2.69/1.03  
% 2.69/1.03  fof(f50,plain,(
% 2.69/1.03    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 2.69/1.03    introduced(choice_axiom,[])).
% 2.69/1.03  
% 2.69/1.03  fof(f51,plain,(
% 2.69/1.03    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 2.69/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f50])).
% 2.69/1.03  
% 2.69/1.03  fof(f81,plain,(
% 2.69/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 2.69/1.03    inference(cnf_transformation,[],[f51])).
% 2.69/1.03  
% 2.69/1.03  fof(f3,axiom,(
% 2.69/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f54,plain,(
% 2.69/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.69/1.03    inference(cnf_transformation,[],[f3])).
% 2.69/1.03  
% 2.69/1.03  fof(f4,axiom,(
% 2.69/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f55,plain,(
% 2.69/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.69/1.03    inference(cnf_transformation,[],[f4])).
% 2.69/1.03  
% 2.69/1.03  fof(f84,plain,(
% 2.69/1.03    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.69/1.03    inference(definition_unfolding,[],[f54,f55])).
% 2.69/1.03  
% 2.69/1.03  fof(f88,plain,(
% 2.69/1.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))),
% 2.69/1.03    inference(definition_unfolding,[],[f81,f84])).
% 2.69/1.03  
% 2.69/1.03  fof(f18,axiom,(
% 2.69/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f39,plain,(
% 2.69/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.03    inference(ennf_transformation,[],[f18])).
% 2.69/1.03  
% 2.69/1.03  fof(f73,plain,(
% 2.69/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.03    inference(cnf_transformation,[],[f39])).
% 2.69/1.03  
% 2.69/1.03  fof(f20,axiom,(
% 2.69/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f41,plain,(
% 2.69/1.03    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.69/1.03    inference(ennf_transformation,[],[f20])).
% 2.69/1.03  
% 2.69/1.03  fof(f42,plain,(
% 2.69/1.03    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.69/1.03    inference(flattening,[],[f41])).
% 2.69/1.03  
% 2.69/1.03  fof(f78,plain,(
% 2.69/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.69/1.03    inference(cnf_transformation,[],[f42])).
% 2.69/1.03  
% 2.69/1.03  fof(f80,plain,(
% 2.69/1.03    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 2.69/1.03    inference(cnf_transformation,[],[f51])).
% 2.69/1.03  
% 2.69/1.03  fof(f89,plain,(
% 2.69/1.03    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 2.69/1.03    inference(definition_unfolding,[],[f80,f84])).
% 2.69/1.03  
% 2.69/1.03  fof(f79,plain,(
% 2.69/1.03    v1_funct_1(sK4)),
% 2.69/1.03    inference(cnf_transformation,[],[f51])).
% 2.69/1.03  
% 2.69/1.03  fof(f82,plain,(
% 2.69/1.03    k1_xboole_0 != sK3),
% 2.69/1.03    inference(cnf_transformation,[],[f51])).
% 2.69/1.03  
% 2.69/1.03  fof(f5,axiom,(
% 2.69/1.03    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f56,plain,(
% 2.69/1.03    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.69/1.03    inference(cnf_transformation,[],[f5])).
% 2.69/1.03  
% 2.69/1.03  fof(f85,plain,(
% 2.69/1.03    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 2.69/1.03    inference(definition_unfolding,[],[f56,f84])).
% 2.69/1.03  
% 2.69/1.03  fof(f16,axiom,(
% 2.69/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f37,plain,(
% 2.69/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.03    inference(ennf_transformation,[],[f16])).
% 2.69/1.03  
% 2.69/1.03  fof(f70,plain,(
% 2.69/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.03    inference(cnf_transformation,[],[f37])).
% 2.69/1.03  
% 2.69/1.03  fof(f8,axiom,(
% 2.69/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f27,plain,(
% 2.69/1.03    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.69/1.03    inference(ennf_transformation,[],[f8])).
% 2.69/1.03  
% 2.69/1.03  fof(f59,plain,(
% 2.69/1.03    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.69/1.03    inference(cnf_transformation,[],[f27])).
% 2.69/1.03  
% 2.69/1.03  fof(f86,plain,(
% 2.69/1.03    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.69/1.03    inference(definition_unfolding,[],[f59,f84])).
% 2.69/1.03  
% 2.69/1.03  fof(f17,axiom,(
% 2.69/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f38,plain,(
% 2.69/1.03    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.69/1.03    inference(ennf_transformation,[],[f17])).
% 2.69/1.03  
% 2.69/1.03  fof(f71,plain,(
% 2.69/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.03    inference(cnf_transformation,[],[f38])).
% 2.69/1.03  
% 2.69/1.03  fof(f11,axiom,(
% 2.69/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f30,plain,(
% 2.69/1.03    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.69/1.03    inference(ennf_transformation,[],[f11])).
% 2.69/1.03  
% 2.69/1.03  fof(f31,plain,(
% 2.69/1.03    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.69/1.03    inference(flattening,[],[f30])).
% 2.69/1.03  
% 2.69/1.03  fof(f63,plain,(
% 2.69/1.03    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.69/1.03    inference(cnf_transformation,[],[f31])).
% 2.69/1.03  
% 2.69/1.03  fof(f9,axiom,(
% 2.69/1.03    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f28,plain,(
% 2.69/1.03    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.69/1.03    inference(ennf_transformation,[],[f9])).
% 2.69/1.03  
% 2.69/1.03  fof(f60,plain,(
% 2.69/1.03    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.69/1.03    inference(cnf_transformation,[],[f28])).
% 2.69/1.03  
% 2.69/1.03  fof(f10,axiom,(
% 2.69/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f29,plain,(
% 2.69/1.03    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.69/1.03    inference(ennf_transformation,[],[f10])).
% 2.69/1.03  
% 2.69/1.03  fof(f47,plain,(
% 2.69/1.03    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.69/1.03    inference(nnf_transformation,[],[f29])).
% 2.69/1.03  
% 2.69/1.03  fof(f62,plain,(
% 2.69/1.03    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.69/1.03    inference(cnf_transformation,[],[f47])).
% 2.69/1.03  
% 2.69/1.03  fof(f72,plain,(
% 2.69/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.69/1.03    inference(cnf_transformation,[],[f38])).
% 2.69/1.03  
% 2.69/1.03  fof(f14,axiom,(
% 2.69/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f34,plain,(
% 2.69/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.69/1.03    inference(ennf_transformation,[],[f14])).
% 2.69/1.03  
% 2.69/1.03  fof(f35,plain,(
% 2.69/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.69/1.03    inference(flattening,[],[f34])).
% 2.69/1.03  
% 2.69/1.03  fof(f68,plain,(
% 2.69/1.03    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.69/1.03    inference(cnf_transformation,[],[f35])).
% 2.69/1.03  
% 2.69/1.03  fof(f83,plain,(
% 2.69/1.03    ~r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 2.69/1.03    inference(cnf_transformation,[],[f51])).
% 2.69/1.03  
% 2.69/1.03  fof(f2,axiom,(
% 2.69/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f53,plain,(
% 2.69/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.69/1.03    inference(cnf_transformation,[],[f2])).
% 2.69/1.03  
% 2.69/1.03  fof(f15,axiom,(
% 2.69/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.69/1.03  
% 2.69/1.03  fof(f36,plain,(
% 2.69/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.69/1.03    inference(ennf_transformation,[],[f15])).
% 2.69/1.03  
% 2.69/1.03  fof(f69,plain,(
% 2.69/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.69/1.03    inference(cnf_transformation,[],[f36])).
% 2.69/1.03  
% 2.69/1.03  cnf(c_0,plain,
% 2.69/1.03      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.69/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1372,plain,
% 2.69/1.03      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_27,negated_conjecture,
% 2.69/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
% 2.69/1.03      inference(cnf_transformation,[],[f88]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1356,plain,
% 2.69/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_19,plain,
% 2.69/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.69/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1361,plain,
% 2.69/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.69/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_2653,plain,
% 2.69/1.03      ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
% 2.69/1.03      inference(superposition,[status(thm)],[c_1356,c_1361]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_24,plain,
% 2.69/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.69/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.03      | ~ r2_hidden(X3,X1)
% 2.69/1.03      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.69/1.03      | ~ v1_funct_1(X0)
% 2.69/1.03      | k1_xboole_0 = X2 ),
% 2.69/1.03      inference(cnf_transformation,[],[f78]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_28,negated_conjecture,
% 2.69/1.03      ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 2.69/1.03      inference(cnf_transformation,[],[f89]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_378,plain,
% 2.69/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.03      | ~ r2_hidden(X3,X1)
% 2.69/1.03      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.69/1.03      | ~ v1_funct_1(X0)
% 2.69/1.03      | k2_enumset1(sK2,sK2,sK2,sK2) != X1
% 2.69/1.03      | sK3 != X2
% 2.69/1.03      | sK4 != X0
% 2.69/1.03      | k1_xboole_0 = X2 ),
% 2.69/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_379,plain,
% 2.69/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 2.69/1.03      | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 2.69/1.03      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
% 2.69/1.03      | ~ v1_funct_1(sK4)
% 2.69/1.03      | k1_xboole_0 = sK3 ),
% 2.69/1.03      inference(unflattening,[status(thm)],[c_378]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_29,negated_conjecture,
% 2.69/1.03      ( v1_funct_1(sK4) ),
% 2.69/1.03      inference(cnf_transformation,[],[f79]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_26,negated_conjecture,
% 2.69/1.03      ( k1_xboole_0 != sK3 ),
% 2.69/1.03      inference(cnf_transformation,[],[f82]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_383,plain,
% 2.69/1.03      ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 2.69/1.03      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) ),
% 2.69/1.03      inference(global_propositional_subsumption,
% 2.69/1.03                [status(thm)],
% 2.69/1.03                [c_379,c_29,c_27,c_26]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1351,plain,
% 2.69/1.03      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 2.69/1.03      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) = iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_2889,plain,
% 2.69/1.03      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 2.69/1.03      | r2_hidden(k1_funct_1(sK4,X0),k2_relat_1(sK4)) = iProver_top ),
% 2.69/1.03      inference(demodulation,[status(thm)],[c_2653,c_1351]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_3078,plain,
% 2.69/1.03      ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),k2_relat_1(sK4)) = iProver_top
% 2.69/1.03      | v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 2.69/1.03      inference(superposition,[status(thm)],[c_1372,c_2889]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_2,plain,
% 2.69/1.03      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 2.69/1.03      inference(cnf_transformation,[],[f85]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1663,plain,
% 2.69/1.03      ( ~ v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 2.69/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1664,plain,
% 2.69/1.03      ( v1_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_1663]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_3805,plain,
% 2.69/1.03      ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),k2_relat_1(sK4)) = iProver_top ),
% 2.69/1.03      inference(global_propositional_subsumption,[status(thm)],[c_3078,c_1664]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_16,plain,
% 2.69/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.69/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1362,plain,
% 2.69/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.69/1.03      | v1_relat_1(X0) = iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1850,plain,
% 2.69/1.03      ( v1_relat_1(sK4) = iProver_top ),
% 2.69/1.03      inference(superposition,[status(thm)],[c_1356,c_1362]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_5,plain,
% 2.69/1.03      ( ~ v1_relat_1(X0)
% 2.69/1.03      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.69/1.03      inference(cnf_transformation,[],[f86]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1368,plain,
% 2.69/1.03      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.69/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_2783,plain,
% 2.69/1.03      ( k9_relat_1(sK4,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 2.69/1.03      inference(superposition,[status(thm)],[c_1850,c_1368]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_18,plain,
% 2.69/1.03      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.69/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_9,plain,
% 2.69/1.03      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.69/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_330,plain,
% 2.69/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.03      | ~ v1_relat_1(X0)
% 2.69/1.03      | k7_relat_1(X0,X1) = X0 ),
% 2.69/1.03      inference(resolution,[status(thm)],[c_18,c_9]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_334,plain,
% 2.69/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.03      | k7_relat_1(X0,X1) = X0 ),
% 2.69/1.03      inference(global_propositional_subsumption,
% 2.69/1.03                [status(thm)],
% 2.69/1.03                [c_330,c_18,c_16,c_9]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1353,plain,
% 2.69/1.03      ( k7_relat_1(X0,X1) = X0
% 2.69/1.03      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_2105,plain,
% 2.69/1.03      ( k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) = sK4 ),
% 2.69/1.03      inference(superposition,[status(thm)],[c_1356,c_1353]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_6,plain,
% 2.69/1.03      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.69/1.03      inference(cnf_transformation,[],[f60]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1367,plain,
% 2.69/1.03      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.69/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_2005,plain,
% 2.69/1.03      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 2.69/1.03      inference(superposition,[status(thm)],[c_1850,c_1367]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_2328,plain,
% 2.69/1.03      ( k9_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) = k2_relat_1(sK4) ),
% 2.69/1.03      inference(superposition,[status(thm)],[c_2105,c_2005]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_2989,plain,
% 2.69/1.03      ( k11_relat_1(sK4,sK2) = k2_relat_1(sK4) ),
% 2.69/1.03      inference(superposition,[status(thm)],[c_2783,c_2328]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_7,plain,
% 2.69/1.03      ( r2_hidden(X0,k1_relat_1(X1))
% 2.69/1.03      | ~ v1_relat_1(X1)
% 2.69/1.03      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 2.69/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1366,plain,
% 2.69/1.03      ( k11_relat_1(X0,X1) = k1_xboole_0
% 2.69/1.03      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 2.69/1.03      | v1_relat_1(X0) != iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_17,plain,
% 2.69/1.03      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.69/1.03      inference(cnf_transformation,[],[f72]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_14,plain,
% 2.69/1.03      ( ~ v5_relat_1(X0,X1)
% 2.69/1.03      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.69/1.03      | r2_hidden(k1_funct_1(X0,X2),X1)
% 2.69/1.03      | ~ v1_funct_1(X0)
% 2.69/1.03      | ~ v1_relat_1(X0) ),
% 2.69/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_350,plain,
% 2.69/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.69/1.03      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.69/1.03      | ~ v1_funct_1(X0)
% 2.69/1.03      | ~ v1_relat_1(X0) ),
% 2.69/1.03      inference(resolution,[status(thm)],[c_17,c_14]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_354,plain,
% 2.69/1.03      ( ~ v1_funct_1(X0)
% 2.69/1.03      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.69/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.69/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.69/1.03      inference(global_propositional_subsumption,[status(thm)],[c_350,c_16]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_355,plain,
% 2.69/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.69/1.03      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.69/1.03      | r2_hidden(k1_funct_1(X0,X3),X2)
% 2.69/1.03      | ~ v1_funct_1(X0) ),
% 2.69/1.03      inference(renaming,[status(thm)],[c_354]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1352,plain,
% 2.69/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.69/1.03      | r2_hidden(X3,k1_relat_1(X0)) != iProver_top
% 2.69/1.03      | r2_hidden(k1_funct_1(X0,X3),X2) = iProver_top
% 2.69/1.03      | v1_funct_1(X0) != iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1657,plain,
% 2.69/1.03      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.69/1.03      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top
% 2.69/1.03      | v1_funct_1(sK4) != iProver_top ),
% 2.69/1.03      inference(superposition,[status(thm)],[c_1356,c_1352]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_30,plain,
% 2.69/1.03      ( v1_funct_1(sK4) = iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1739,plain,
% 2.69/1.03      ( r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top
% 2.69/1.03      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.69/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1657,c_30]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1740,plain,
% 2.69/1.03      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.69/1.03      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
% 2.69/1.03      inference(renaming,[status(thm)],[c_1739]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_25,negated_conjecture,
% 2.69/1.03      ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
% 2.69/1.03      inference(cnf_transformation,[],[f83]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1357,plain,
% 2.69/1.03      ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1747,plain,
% 2.69/1.03      ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top ),
% 2.69/1.03      inference(superposition,[status(thm)],[c_1740,c_1357]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_2855,plain,
% 2.69/1.03      ( k11_relat_1(sK4,sK2) = k1_xboole_0 | v1_relat_1(sK4) != iProver_top ),
% 2.69/1.03      inference(superposition,[status(thm)],[c_1366,c_1747]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_32,plain,
% 2.69/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1545,plain,
% 2.69/1.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 2.69/1.03      | v1_relat_1(sK4) ),
% 2.69/1.03      inference(instantiation,[status(thm)],[c_16]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1546,plain,
% 2.69/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top
% 2.69/1.03      | v1_relat_1(sK4) = iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_1545]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_3002,plain,
% 2.69/1.03      ( k11_relat_1(sK4,sK2) = k1_xboole_0 ),
% 2.69/1.03      inference(global_propositional_subsumption,
% 2.69/1.03                [status(thm)],
% 2.69/1.03                [c_2855,c_32,c_1546]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_3164,plain,
% 2.69/1.03      ( k2_relat_1(sK4) = k1_xboole_0 ),
% 2.69/1.03      inference(light_normalisation,[status(thm)],[c_2989,c_3002]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_3809,plain,
% 2.69/1.03      ( r2_hidden(k1_funct_1(sK4,sK0(k2_enumset1(sK2,sK2,sK2,sK2))),k1_xboole_0) = iProver_top ),
% 2.69/1.03      inference(light_normalisation,[status(thm)],[c_3805,c_3164]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1,plain,
% 2.69/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 2.69/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_15,plain,
% 2.69/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.69/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_319,plain,
% 2.69/1.03      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.69/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_320,plain,
% 2.69/1.03      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.69/1.03      inference(unflattening,[status(thm)],[c_319]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_1354,plain,
% 2.69/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.69/1.03      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 2.69/1.03  
% 2.69/1.03  cnf(c_3811,plain,
% 2.69/1.03      ( $false ),
% 2.69/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_3809,c_1354]) ).
% 2.69/1.03  
% 2.69/1.03  
% 2.69/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.69/1.03  
% 2.69/1.03  ------                               Statistics
% 2.69/1.03  
% 2.69/1.03  ------ General
% 2.69/1.03  
% 2.69/1.03  abstr_ref_over_cycles:                  0
% 2.69/1.03  abstr_ref_under_cycles:                 0
% 2.69/1.03  gc_basic_clause_elim:                   0
% 2.69/1.03  forced_gc_time:                         0
% 2.69/1.03  parsing_time:                           0.008
% 2.69/1.03  unif_index_cands_time:                  0.
% 2.69/1.03  unif_index_add_time:                    0.
% 2.69/1.03  orderings_time:                         0.
% 2.69/1.03  out_proof_time:                         0.009
% 2.69/1.03  total_time:                             0.161
% 2.69/1.03  num_of_symbols:                         56
% 2.69/1.03  num_of_terms:                           3585
% 2.69/1.03  
% 2.69/1.03  ------ Preprocessing
% 2.69/1.03  
% 2.69/1.03  num_of_splits:                          0
% 2.69/1.03  num_of_split_atoms:                     0
% 2.69/1.03  num_of_reused_defs:                     0
% 2.69/1.03  num_eq_ax_congr_red:                    29
% 2.69/1.03  num_of_sem_filtered_clauses:            1
% 2.69/1.03  num_of_subtypes:                        0
% 2.69/1.03  monotx_restored_types:                  0
% 2.69/1.03  sat_num_of_epr_types:                   0
% 2.69/1.03  sat_num_of_non_cyclic_types:            0
% 2.69/1.03  sat_guarded_non_collapsed_types:        0
% 2.69/1.03  num_pure_diseq_elim:                    0
% 2.69/1.03  simp_replaced_by:                       0
% 2.69/1.03  res_preprocessed:                       139
% 2.69/1.03  prep_upred:                             0
% 2.69/1.03  prep_unflattend:                        27
% 2.69/1.03  smt_new_axioms:                         0
% 2.69/1.03  pred_elim_cands:                        5
% 2.69/1.03  pred_elim:                              4
% 2.69/1.03  pred_elim_cl:                           4
% 2.69/1.03  pred_elim_cycles:                       10
% 2.69/1.03  merged_defs:                            0
% 2.69/1.03  merged_defs_ncl:                        0
% 2.69/1.03  bin_hyper_res:                          0
% 2.69/1.03  prep_cycles:                            4
% 2.69/1.03  pred_elim_time:                         0.013
% 2.69/1.03  splitting_time:                         0.
% 2.69/1.03  sem_filter_time:                        0.
% 2.69/1.03  monotx_time:                            0.
% 2.69/1.03  subtype_inf_time:                       0.
% 2.69/1.03  
% 2.69/1.03  ------ Problem properties
% 2.69/1.03  
% 2.69/1.03  clauses:                                26
% 2.69/1.03  conjectures:                            4
% 2.69/1.03  epr:                                    3
% 2.69/1.03  horn:                                   24
% 2.69/1.03  ground:                                 6
% 2.69/1.03  unary:                                  12
% 2.69/1.03  binary:                                 8
% 2.69/1.03  lits:                                   47
% 2.69/1.03  lits_eq:                                15
% 2.69/1.03  fd_pure:                                0
% 2.69/1.03  fd_pseudo:                              0
% 2.69/1.03  fd_cond:                                2
% 2.69/1.03  fd_pseudo_cond:                         0
% 2.69/1.03  ac_symbols:                             0
% 2.69/1.03  
% 2.69/1.03  ------ Propositional Solver
% 2.69/1.03  
% 2.69/1.03  prop_solver_calls:                      28
% 2.69/1.03  prop_fast_solver_calls:                 780
% 2.69/1.03  smt_solver_calls:                       0
% 2.69/1.03  smt_fast_solver_calls:                  0
% 2.69/1.03  prop_num_of_clauses:                    1449
% 2.69/1.03  prop_preprocess_simplified:             5342
% 2.69/1.03  prop_fo_subsumed:                       13
% 2.69/1.03  prop_solver_time:                       0.
% 2.69/1.03  smt_solver_time:                        0.
% 2.69/1.03  smt_fast_solver_time:                   0.
% 2.69/1.03  prop_fast_solver_time:                  0.
% 2.69/1.03  prop_unsat_core_time:                   0.
% 2.69/1.03  
% 2.69/1.03  ------ QBF
% 2.69/1.03  
% 2.69/1.03  qbf_q_res:                              0
% 2.69/1.03  qbf_num_tautologies:                    0
% 2.69/1.03  qbf_prep_cycles:                        0
% 2.69/1.03  
% 2.69/1.03  ------ BMC1
% 2.69/1.03  
% 2.69/1.03  bmc1_current_bound:                     -1
% 2.69/1.03  bmc1_last_solved_bound:                 -1
% 2.69/1.03  bmc1_unsat_core_size:                   -1
% 2.69/1.03  bmc1_unsat_core_parents_size:           -1
% 2.69/1.03  bmc1_merge_next_fun:                    0
% 2.69/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.69/1.03  
% 2.69/1.03  ------ Instantiation
% 2.69/1.03  
% 2.69/1.03  inst_num_of_clauses:                    470
% 2.69/1.03  inst_num_in_passive:                    131
% 2.69/1.03  inst_num_in_active:                     230
% 2.69/1.03  inst_num_in_unprocessed:                109
% 2.69/1.03  inst_num_of_loops:                      280
% 2.69/1.03  inst_num_of_learning_restarts:          0
% 2.69/1.03  inst_num_moves_active_passive:          47
% 2.69/1.03  inst_lit_activity:                      0
% 2.69/1.03  inst_lit_activity_moves:                0
% 2.69/1.03  inst_num_tautologies:                   0
% 2.69/1.03  inst_num_prop_implied:                  0
% 2.69/1.03  inst_num_existing_simplified:           0
% 2.69/1.03  inst_num_eq_res_simplified:             0
% 2.69/1.03  inst_num_child_elim:                    0
% 2.69/1.03  inst_num_of_dismatching_blockings:      94
% 2.69/1.03  inst_num_of_non_proper_insts:           325
% 2.69/1.03  inst_num_of_duplicates:                 0
% 2.69/1.03  inst_inst_num_from_inst_to_res:         0
% 2.69/1.03  inst_dismatching_checking_time:         0.
% 2.69/1.03  
% 2.69/1.03  ------ Resolution
% 2.69/1.03  
% 2.69/1.03  res_num_of_clauses:                     0
% 2.69/1.03  res_num_in_passive:                     0
% 2.69/1.03  res_num_in_active:                      0
% 2.69/1.03  res_num_of_loops:                       143
% 2.69/1.03  res_forward_subset_subsumed:            23
% 2.69/1.03  res_backward_subset_subsumed:           0
% 2.69/1.03  res_forward_subsumed:                   0
% 2.69/1.03  res_backward_subsumed:                  0
% 2.69/1.03  res_forward_subsumption_resolution:     0
% 2.69/1.03  res_backward_subsumption_resolution:    0
% 2.69/1.03  res_clause_to_clause_subsumption:       96
% 2.69/1.03  res_orphan_elimination:                 0
% 2.69/1.03  res_tautology_del:                      22
% 2.69/1.03  res_num_eq_res_simplified:              0
% 2.69/1.03  res_num_sel_changes:                    0
% 2.69/1.03  res_moves_from_active_to_pass:          0
% 2.69/1.03  
% 2.69/1.03  ------ Superposition
% 2.69/1.03  
% 2.69/1.03  sup_time_total:                         0.
% 2.69/1.03  sup_time_generating:                    0.
% 2.69/1.03  sup_time_sim_full:                      0.
% 2.69/1.03  sup_time_sim_immed:                     0.
% 2.69/1.03  
% 2.69/1.03  sup_num_of_clauses:                     63
% 2.69/1.03  sup_num_in_active:                      49
% 2.69/1.03  sup_num_in_passive:                     14
% 2.69/1.03  sup_num_of_loops:                       55
% 2.69/1.03  sup_fw_superposition:                   32
% 2.69/1.03  sup_bw_superposition:                   20
% 2.69/1.03  sup_immediate_simplified:               18
% 2.69/1.03  sup_given_eliminated:                   0
% 2.69/1.03  comparisons_done:                       0
% 2.69/1.03  comparisons_avoided:                    0
% 2.69/1.03  
% 2.69/1.03  ------ Simplifications
% 2.69/1.03  
% 2.69/1.03  
% 2.69/1.03  sim_fw_subset_subsumed:                 4
% 2.69/1.03  sim_bw_subset_subsumed:                 0
% 2.69/1.03  sim_fw_subsumed:                        4
% 2.69/1.03  sim_bw_subsumed:                        0
% 2.69/1.03  sim_fw_subsumption_res:                 1
% 2.69/1.03  sim_bw_subsumption_res:                 0
% 2.69/1.03  sim_tautology_del:                      0
% 2.69/1.03  sim_eq_tautology_del:                   3
% 2.69/1.03  sim_eq_res_simp:                        1
% 2.69/1.03  sim_fw_demodulated:                     4
% 2.69/1.03  sim_bw_demodulated:                     7
% 2.69/1.03  sim_light_normalised:                   14
% 2.69/1.03  sim_joinable_taut:                      0
% 2.69/1.03  sim_joinable_simp:                      0
% 2.69/1.03  sim_ac_normalised:                      0
% 2.69/1.03  sim_smt_subsumption:                    0
% 2.69/1.03  
%------------------------------------------------------------------------------
