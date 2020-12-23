%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:38 EST 2020

% Result     : CounterSatisfiable 2.17s
% Output     : Saturation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  177 (6710 expanded)
%              Number of clauses        :  104 (1637 expanded)
%              Number of leaves         :   24 (1517 expanded)
%              Depth                    :   28
%              Number of atoms          :  399 (15954 expanded)
%              Number of equality atoms :  233 (6286 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f73])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f65,f74])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f22,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f44,plain,
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

fof(f45,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f70,f74])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f72,f74,f74])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_218,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_216,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_208,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_745,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1028,plain,
    ( k11_relat_1(X0,X1) = k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_285,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_286,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_285])).

cnf(c_1019,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_287,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_286])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1150,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1151,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1150])).

cnf(c_1156,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1019,c_25,c_287,c_1151])).

cnf(c_1157,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1156])).

cnf(c_2193,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k11_relat_1(sK3,X0) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_1157])).

cnf(c_2200,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k11_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2193])).

cnf(c_2368,plain,
    ( k11_relat_1(sK3,X0) = k1_xboole_0
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2193,c_22,c_1150,c_2200])).

cnf(c_2369,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k11_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2368])).

cnf(c_1022,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1023,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1633,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1022,c_1023])).

cnf(c_1024,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1318,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_1024])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1029,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1374,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1318,c_1029])).

cnf(c_4,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_246,plain,
    ( ~ v1_relat_1(X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(X0,X1)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(X0) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_1021,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(X0,X1)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_1424,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(k7_relat_1(sK3,X0),X1)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k9_relat_1(sK3,X0)
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_1021])).

cnf(c_1804,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k9_relat_1(sK3,X0)
    | k9_relat_1(k7_relat_1(sK3,X0),X1) != k9_relat_1(sK3,sK2)
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1633,c_1424])).

cnf(c_2373,plain,
    ( k9_relat_1(k7_relat_1(sK3,X0),X1) != k9_relat_1(sK3,sK2)
    | k9_relat_1(sK3,X0) != k11_relat_1(sK3,sK0)
    | k11_relat_1(sK3,sK0) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2369,c_1804])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_265,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_18,c_11])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_265,c_18,c_17,c_11])).

cnf(c_1020,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_1254,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = sK3 ),
    inference(superposition,[status(thm)],[c_1022,c_1020])).

cnf(c_1423,plain,
    ( k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1254,c_1374])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1030,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1741,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1318,c_1030])).

cnf(c_1887,plain,
    ( k11_relat_1(sK3,sK0) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1423,c_1741])).

cnf(c_2394,plain,
    ( k9_relat_1(k7_relat_1(sK3,X0),X1) != k9_relat_1(sK3,sK2)
    | k9_relat_1(sK3,X0) != k2_relat_1(sK3)
    | k11_relat_1(sK3,sK0) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2373,c_1887])).

cnf(c_2395,plain,
    ( k9_relat_1(k7_relat_1(sK3,X0),X1) != k9_relat_1(sK3,sK2)
    | k9_relat_1(sK3,X0) != k2_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2394,c_1887])).

cnf(c_1805,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(X0)
    | k9_relat_1(X0,X1) != k9_relat_1(sK3,sK2)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1633,c_1021])).

cnf(c_2374,plain,
    ( k9_relat_1(X0,X1) != k9_relat_1(sK3,sK2)
    | k11_relat_1(sK3,sK0) != k2_relat_1(X0)
    | k11_relat_1(sK3,sK0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2369,c_1805])).

cnf(c_2384,plain,
    ( k9_relat_1(X0,X1) != k9_relat_1(sK3,sK2)
    | k11_relat_1(sK3,sK0) = k1_xboole_0
    | k2_relat_1(X0) != k2_relat_1(sK3)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2374,c_1887])).

cnf(c_2385,plain,
    ( k9_relat_1(X0,X1) != k9_relat_1(sK3,sK2)
    | k2_relat_1(X0) != k2_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2384,c_1887])).

cnf(c_2593,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2385])).

cnf(c_2594,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2593])).

cnf(c_2704,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2395,c_25,c_1151,c_2594])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1026,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2719,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2704,c_1026])).

cnf(c_2262,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2825,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2719,c_22,c_25,c_1150,c_1151,c_2262,c_2594])).

cnf(c_2829,plain,
    ( k11_relat_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2825,c_1028])).

cnf(c_1142,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1144,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1142])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1143,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1146,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1143])).

cnf(c_1032,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1317,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1032,c_1024])).

cnf(c_1740,plain,
    ( k9_relat_1(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1317,c_1030])).

cnf(c_6,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1745,plain,
    ( k11_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1740,c_6])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1027,plain,
    ( k11_relat_1(X0,X1) != k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2115,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1745,c_1027])).

cnf(c_13,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2118,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2115,c_13])).

cnf(c_2841,plain,
    ( k11_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2829,c_25,c_1144,c_1146,c_1151,c_2118])).

cnf(c_1727,plain,
    ( k9_relat_1(sK3,X0) != k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_1026])).

cnf(c_2043,plain,
    ( k11_relat_1(sK3,X0) != k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1741,c_1727])).

cnf(c_2849,plain,
    ( k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2841,c_2043])).

cnf(c_2853,plain,
    ( k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2849])).

cnf(c_2850,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2841,c_1741])).

cnf(c_1965,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k11_relat_1(sK3,X0)
    | k9_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)),X1) != k9_relat_1(sK3,sK2)
    | v1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1741,c_1804])).

cnf(c_2847,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k1_xboole_0
    | k9_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)),X1) != k9_relat_1(sK3,sK2)
    | v1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2841,c_1965])).

cnf(c_2710,plain,
    ( k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2704,c_1423])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1031,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2291,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | m1_subset_1(X0,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_1031])).

cnf(c_2181,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2118,c_1144,c_1146])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_241,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k1_xboole_0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_242,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_1806,plain,
    ( k9_relat_1(sK3,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1633,c_242])).

cnf(c_1632,plain,
    ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1032,c_1023])).

cnf(c_1637,plain,
    ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1632,c_6])).

cnf(c_1257,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1032,c_1020])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1025,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_12,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:54:01 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.17/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/0.99  
% 2.17/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.17/0.99  
% 2.17/0.99  ------  iProver source info
% 2.17/0.99  
% 2.17/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.17/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.17/0.99  git: non_committed_changes: false
% 2.17/0.99  git: last_make_outside_of_git: false
% 2.17/0.99  
% 2.17/0.99  ------ 
% 2.17/0.99  
% 2.17/0.99  ------ Input Options
% 2.17/0.99  
% 2.17/0.99  --out_options                           all
% 2.17/0.99  --tptp_safe_out                         true
% 2.17/0.99  --problem_path                          ""
% 2.17/0.99  --include_path                          ""
% 2.17/0.99  --clausifier                            res/vclausify_rel
% 2.17/0.99  --clausifier_options                    --mode clausify
% 2.17/0.99  --stdin                                 false
% 2.17/0.99  --stats_out                             all
% 2.17/0.99  
% 2.17/0.99  ------ General Options
% 2.17/0.99  
% 2.17/0.99  --fof                                   false
% 2.17/0.99  --time_out_real                         305.
% 2.17/0.99  --time_out_virtual                      -1.
% 2.17/0.99  --symbol_type_check                     false
% 2.17/0.99  --clausify_out                          false
% 2.17/0.99  --sig_cnt_out                           false
% 2.17/0.99  --trig_cnt_out                          false
% 2.17/0.99  --trig_cnt_out_tolerance                1.
% 2.17/0.99  --trig_cnt_out_sk_spl                   false
% 2.17/0.99  --abstr_cl_out                          false
% 2.17/0.99  
% 2.17/0.99  ------ Global Options
% 2.17/0.99  
% 2.17/0.99  --schedule                              default
% 2.17/0.99  --add_important_lit                     false
% 2.17/0.99  --prop_solver_per_cl                    1000
% 2.17/0.99  --min_unsat_core                        false
% 2.17/0.99  --soft_assumptions                      false
% 2.17/0.99  --soft_lemma_size                       3
% 2.17/0.99  --prop_impl_unit_size                   0
% 2.17/0.99  --prop_impl_unit                        []
% 2.17/0.99  --share_sel_clauses                     true
% 2.17/0.99  --reset_solvers                         false
% 2.17/0.99  --bc_imp_inh                            [conj_cone]
% 2.17/0.99  --conj_cone_tolerance                   3.
% 2.17/0.99  --extra_neg_conj                        none
% 2.17/0.99  --large_theory_mode                     true
% 2.17/0.99  --prolific_symb_bound                   200
% 2.17/0.99  --lt_threshold                          2000
% 2.17/0.99  --clause_weak_htbl                      true
% 2.17/0.99  --gc_record_bc_elim                     false
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing Options
% 2.17/0.99  
% 2.17/0.99  --preprocessing_flag                    true
% 2.17/0.99  --time_out_prep_mult                    0.1
% 2.17/0.99  --splitting_mode                        input
% 2.17/0.99  --splitting_grd                         true
% 2.17/0.99  --splitting_cvd                         false
% 2.17/0.99  --splitting_cvd_svl                     false
% 2.17/0.99  --splitting_nvd                         32
% 2.17/0.99  --sub_typing                            true
% 2.17/0.99  --prep_gs_sim                           true
% 2.17/0.99  --prep_unflatten                        true
% 2.17/0.99  --prep_res_sim                          true
% 2.17/0.99  --prep_upred                            true
% 2.17/0.99  --prep_sem_filter                       exhaustive
% 2.17/0.99  --prep_sem_filter_out                   false
% 2.17/0.99  --pred_elim                             true
% 2.17/0.99  --res_sim_input                         true
% 2.17/0.99  --eq_ax_congr_red                       true
% 2.17/0.99  --pure_diseq_elim                       true
% 2.17/0.99  --brand_transform                       false
% 2.17/0.99  --non_eq_to_eq                          false
% 2.17/0.99  --prep_def_merge                        true
% 2.17/0.99  --prep_def_merge_prop_impl              false
% 2.17/0.99  --prep_def_merge_mbd                    true
% 2.17/0.99  --prep_def_merge_tr_red                 false
% 2.17/0.99  --prep_def_merge_tr_cl                  false
% 2.17/0.99  --smt_preprocessing                     true
% 2.17/0.99  --smt_ac_axioms                         fast
% 2.17/0.99  --preprocessed_out                      false
% 2.17/0.99  --preprocessed_stats                    false
% 2.17/0.99  
% 2.17/0.99  ------ Abstraction refinement Options
% 2.17/0.99  
% 2.17/0.99  --abstr_ref                             []
% 2.17/0.99  --abstr_ref_prep                        false
% 2.17/0.99  --abstr_ref_until_sat                   false
% 2.17/0.99  --abstr_ref_sig_restrict                funpre
% 2.17/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.99  --abstr_ref_under                       []
% 2.17/0.99  
% 2.17/0.99  ------ SAT Options
% 2.17/0.99  
% 2.17/0.99  --sat_mode                              false
% 2.17/0.99  --sat_fm_restart_options                ""
% 2.17/0.99  --sat_gr_def                            false
% 2.17/0.99  --sat_epr_types                         true
% 2.17/0.99  --sat_non_cyclic_types                  false
% 2.17/0.99  --sat_finite_models                     false
% 2.17/0.99  --sat_fm_lemmas                         false
% 2.17/0.99  --sat_fm_prep                           false
% 2.17/0.99  --sat_fm_uc_incr                        true
% 2.17/0.99  --sat_out_model                         small
% 2.17/0.99  --sat_out_clauses                       false
% 2.17/0.99  
% 2.17/0.99  ------ QBF Options
% 2.17/0.99  
% 2.17/0.99  --qbf_mode                              false
% 2.17/0.99  --qbf_elim_univ                         false
% 2.17/0.99  --qbf_dom_inst                          none
% 2.17/0.99  --qbf_dom_pre_inst                      false
% 2.17/0.99  --qbf_sk_in                             false
% 2.17/0.99  --qbf_pred_elim                         true
% 2.17/0.99  --qbf_split                             512
% 2.17/0.99  
% 2.17/0.99  ------ BMC1 Options
% 2.17/0.99  
% 2.17/0.99  --bmc1_incremental                      false
% 2.17/0.99  --bmc1_axioms                           reachable_all
% 2.17/0.99  --bmc1_min_bound                        0
% 2.17/0.99  --bmc1_max_bound                        -1
% 2.17/0.99  --bmc1_max_bound_default                -1
% 2.17/0.99  --bmc1_symbol_reachability              true
% 2.17/0.99  --bmc1_property_lemmas                  false
% 2.17/0.99  --bmc1_k_induction                      false
% 2.17/0.99  --bmc1_non_equiv_states                 false
% 2.17/0.99  --bmc1_deadlock                         false
% 2.17/0.99  --bmc1_ucm                              false
% 2.17/0.99  --bmc1_add_unsat_core                   none
% 2.17/0.99  --bmc1_unsat_core_children              false
% 2.17/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.99  --bmc1_out_stat                         full
% 2.17/0.99  --bmc1_ground_init                      false
% 2.17/0.99  --bmc1_pre_inst_next_state              false
% 2.17/0.99  --bmc1_pre_inst_state                   false
% 2.17/0.99  --bmc1_pre_inst_reach_state             false
% 2.17/0.99  --bmc1_out_unsat_core                   false
% 2.17/0.99  --bmc1_aig_witness_out                  false
% 2.17/0.99  --bmc1_verbose                          false
% 2.17/0.99  --bmc1_dump_clauses_tptp                false
% 2.17/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.99  --bmc1_dump_file                        -
% 2.17/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.99  --bmc1_ucm_extend_mode                  1
% 2.17/0.99  --bmc1_ucm_init_mode                    2
% 2.17/0.99  --bmc1_ucm_cone_mode                    none
% 2.17/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.99  --bmc1_ucm_relax_model                  4
% 2.17/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.99  --bmc1_ucm_layered_model                none
% 2.17/0.99  --bmc1_ucm_max_lemma_size               10
% 2.17/0.99  
% 2.17/0.99  ------ AIG Options
% 2.17/0.99  
% 2.17/0.99  --aig_mode                              false
% 2.17/0.99  
% 2.17/0.99  ------ Instantiation Options
% 2.17/0.99  
% 2.17/0.99  --instantiation_flag                    true
% 2.17/0.99  --inst_sos_flag                         false
% 2.17/0.99  --inst_sos_phase                        true
% 2.17/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.99  --inst_lit_sel_side                     num_symb
% 2.17/0.99  --inst_solver_per_active                1400
% 2.17/0.99  --inst_solver_calls_frac                1.
% 2.17/0.99  --inst_passive_queue_type               priority_queues
% 2.17/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.99  --inst_passive_queues_freq              [25;2]
% 2.17/0.99  --inst_dismatching                      true
% 2.17/0.99  --inst_eager_unprocessed_to_passive     true
% 2.17/0.99  --inst_prop_sim_given                   true
% 2.17/0.99  --inst_prop_sim_new                     false
% 2.17/0.99  --inst_subs_new                         false
% 2.17/0.99  --inst_eq_res_simp                      false
% 2.17/0.99  --inst_subs_given                       false
% 2.17/0.99  --inst_orphan_elimination               true
% 2.17/0.99  --inst_learning_loop_flag               true
% 2.17/0.99  --inst_learning_start                   3000
% 2.17/0.99  --inst_learning_factor                  2
% 2.17/0.99  --inst_start_prop_sim_after_learn       3
% 2.17/0.99  --inst_sel_renew                        solver
% 2.17/0.99  --inst_lit_activity_flag                true
% 2.17/0.99  --inst_restr_to_given                   false
% 2.17/0.99  --inst_activity_threshold               500
% 2.17/0.99  --inst_out_proof                        true
% 2.17/0.99  
% 2.17/0.99  ------ Resolution Options
% 2.17/0.99  
% 2.17/0.99  --resolution_flag                       true
% 2.17/0.99  --res_lit_sel                           adaptive
% 2.17/0.99  --res_lit_sel_side                      none
% 2.17/0.99  --res_ordering                          kbo
% 2.17/0.99  --res_to_prop_solver                    active
% 2.17/0.99  --res_prop_simpl_new                    false
% 2.17/0.99  --res_prop_simpl_given                  true
% 2.17/0.99  --res_passive_queue_type                priority_queues
% 2.17/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.99  --res_passive_queues_freq               [15;5]
% 2.17/0.99  --res_forward_subs                      full
% 2.17/0.99  --res_backward_subs                     full
% 2.17/0.99  --res_forward_subs_resolution           true
% 2.17/0.99  --res_backward_subs_resolution          true
% 2.17/0.99  --res_orphan_elimination                true
% 2.17/0.99  --res_time_limit                        2.
% 2.17/0.99  --res_out_proof                         true
% 2.17/0.99  
% 2.17/0.99  ------ Superposition Options
% 2.17/0.99  
% 2.17/0.99  --superposition_flag                    true
% 2.17/0.99  --sup_passive_queue_type                priority_queues
% 2.17/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.99  --demod_completeness_check              fast
% 2.17/0.99  --demod_use_ground                      true
% 2.17/0.99  --sup_to_prop_solver                    passive
% 2.17/0.99  --sup_prop_simpl_new                    true
% 2.17/0.99  --sup_prop_simpl_given                  true
% 2.17/0.99  --sup_fun_splitting                     false
% 2.17/0.99  --sup_smt_interval                      50000
% 2.17/0.99  
% 2.17/0.99  ------ Superposition Simplification Setup
% 2.17/0.99  
% 2.17/0.99  --sup_indices_passive                   []
% 2.17/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.99  --sup_full_bw                           [BwDemod]
% 2.17/0.99  --sup_immed_triv                        [TrivRules]
% 2.17/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.99  --sup_immed_bw_main                     []
% 2.17/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.99  
% 2.17/0.99  ------ Combination Options
% 2.17/0.99  
% 2.17/0.99  --comb_res_mult                         3
% 2.17/0.99  --comb_sup_mult                         2
% 2.17/0.99  --comb_inst_mult                        10
% 2.17/0.99  
% 2.17/0.99  ------ Debug Options
% 2.17/0.99  
% 2.17/0.99  --dbg_backtrace                         false
% 2.17/0.99  --dbg_dump_prop_clauses                 false
% 2.17/0.99  --dbg_dump_prop_clauses_file            -
% 2.17/0.99  --dbg_out_stat                          false
% 2.17/0.99  ------ Parsing...
% 2.17/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.17/0.99  ------ Proving...
% 2.17/0.99  ------ Problem Properties 
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  clauses                                 19
% 2.17/0.99  conjectures                             2
% 2.17/0.99  EPR                                     1
% 2.17/0.99  Horn                                    18
% 2.17/0.99  unary                                   7
% 2.17/0.99  binary                                  5
% 2.17/0.99  lits                                    38
% 2.17/0.99  lits eq                                 18
% 2.17/0.99  fd_pure                                 0
% 2.17/0.99  fd_pseudo                               0
% 2.17/0.99  fd_cond                                 0
% 2.17/0.99  fd_pseudo_cond                          0
% 2.17/0.99  AC symbols                              0
% 2.17/0.99  
% 2.17/0.99  ------ Schedule dynamic 5 is on 
% 2.17/0.99  
% 2.17/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  ------ 
% 2.17/0.99  Current options:
% 2.17/0.99  ------ 
% 2.17/0.99  
% 2.17/0.99  ------ Input Options
% 2.17/0.99  
% 2.17/0.99  --out_options                           all
% 2.17/0.99  --tptp_safe_out                         true
% 2.17/0.99  --problem_path                          ""
% 2.17/0.99  --include_path                          ""
% 2.17/0.99  --clausifier                            res/vclausify_rel
% 2.17/0.99  --clausifier_options                    --mode clausify
% 2.17/0.99  --stdin                                 false
% 2.17/0.99  --stats_out                             all
% 2.17/0.99  
% 2.17/0.99  ------ General Options
% 2.17/0.99  
% 2.17/0.99  --fof                                   false
% 2.17/0.99  --time_out_real                         305.
% 2.17/0.99  --time_out_virtual                      -1.
% 2.17/0.99  --symbol_type_check                     false
% 2.17/0.99  --clausify_out                          false
% 2.17/0.99  --sig_cnt_out                           false
% 2.17/0.99  --trig_cnt_out                          false
% 2.17/0.99  --trig_cnt_out_tolerance                1.
% 2.17/0.99  --trig_cnt_out_sk_spl                   false
% 2.17/0.99  --abstr_cl_out                          false
% 2.17/0.99  
% 2.17/0.99  ------ Global Options
% 2.17/0.99  
% 2.17/0.99  --schedule                              default
% 2.17/0.99  --add_important_lit                     false
% 2.17/0.99  --prop_solver_per_cl                    1000
% 2.17/0.99  --min_unsat_core                        false
% 2.17/0.99  --soft_assumptions                      false
% 2.17/0.99  --soft_lemma_size                       3
% 2.17/0.99  --prop_impl_unit_size                   0
% 2.17/0.99  --prop_impl_unit                        []
% 2.17/0.99  --share_sel_clauses                     true
% 2.17/0.99  --reset_solvers                         false
% 2.17/0.99  --bc_imp_inh                            [conj_cone]
% 2.17/0.99  --conj_cone_tolerance                   3.
% 2.17/0.99  --extra_neg_conj                        none
% 2.17/0.99  --large_theory_mode                     true
% 2.17/0.99  --prolific_symb_bound                   200
% 2.17/0.99  --lt_threshold                          2000
% 2.17/0.99  --clause_weak_htbl                      true
% 2.17/0.99  --gc_record_bc_elim                     false
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing Options
% 2.17/0.99  
% 2.17/0.99  --preprocessing_flag                    true
% 2.17/0.99  --time_out_prep_mult                    0.1
% 2.17/0.99  --splitting_mode                        input
% 2.17/0.99  --splitting_grd                         true
% 2.17/0.99  --splitting_cvd                         false
% 2.17/0.99  --splitting_cvd_svl                     false
% 2.17/0.99  --splitting_nvd                         32
% 2.17/0.99  --sub_typing                            true
% 2.17/0.99  --prep_gs_sim                           true
% 2.17/0.99  --prep_unflatten                        true
% 2.17/0.99  --prep_res_sim                          true
% 2.17/0.99  --prep_upred                            true
% 2.17/0.99  --prep_sem_filter                       exhaustive
% 2.17/0.99  --prep_sem_filter_out                   false
% 2.17/0.99  --pred_elim                             true
% 2.17/0.99  --res_sim_input                         true
% 2.17/0.99  --eq_ax_congr_red                       true
% 2.17/0.99  --pure_diseq_elim                       true
% 2.17/0.99  --brand_transform                       false
% 2.17/0.99  --non_eq_to_eq                          false
% 2.17/0.99  --prep_def_merge                        true
% 2.17/0.99  --prep_def_merge_prop_impl              false
% 2.17/0.99  --prep_def_merge_mbd                    true
% 2.17/0.99  --prep_def_merge_tr_red                 false
% 2.17/0.99  --prep_def_merge_tr_cl                  false
% 2.17/0.99  --smt_preprocessing                     true
% 2.17/0.99  --smt_ac_axioms                         fast
% 2.17/0.99  --preprocessed_out                      false
% 2.17/0.99  --preprocessed_stats                    false
% 2.17/0.99  
% 2.17/0.99  ------ Abstraction refinement Options
% 2.17/0.99  
% 2.17/0.99  --abstr_ref                             []
% 2.17/0.99  --abstr_ref_prep                        false
% 2.17/0.99  --abstr_ref_until_sat                   false
% 2.17/0.99  --abstr_ref_sig_restrict                funpre
% 2.17/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/0.99  --abstr_ref_under                       []
% 2.17/0.99  
% 2.17/0.99  ------ SAT Options
% 2.17/0.99  
% 2.17/0.99  --sat_mode                              false
% 2.17/0.99  --sat_fm_restart_options                ""
% 2.17/0.99  --sat_gr_def                            false
% 2.17/0.99  --sat_epr_types                         true
% 2.17/0.99  --sat_non_cyclic_types                  false
% 2.17/0.99  --sat_finite_models                     false
% 2.17/0.99  --sat_fm_lemmas                         false
% 2.17/0.99  --sat_fm_prep                           false
% 2.17/0.99  --sat_fm_uc_incr                        true
% 2.17/0.99  --sat_out_model                         small
% 2.17/0.99  --sat_out_clauses                       false
% 2.17/0.99  
% 2.17/0.99  ------ QBF Options
% 2.17/0.99  
% 2.17/0.99  --qbf_mode                              false
% 2.17/0.99  --qbf_elim_univ                         false
% 2.17/0.99  --qbf_dom_inst                          none
% 2.17/0.99  --qbf_dom_pre_inst                      false
% 2.17/0.99  --qbf_sk_in                             false
% 2.17/0.99  --qbf_pred_elim                         true
% 2.17/0.99  --qbf_split                             512
% 2.17/0.99  
% 2.17/0.99  ------ BMC1 Options
% 2.17/0.99  
% 2.17/0.99  --bmc1_incremental                      false
% 2.17/0.99  --bmc1_axioms                           reachable_all
% 2.17/0.99  --bmc1_min_bound                        0
% 2.17/0.99  --bmc1_max_bound                        -1
% 2.17/0.99  --bmc1_max_bound_default                -1
% 2.17/0.99  --bmc1_symbol_reachability              true
% 2.17/0.99  --bmc1_property_lemmas                  false
% 2.17/0.99  --bmc1_k_induction                      false
% 2.17/0.99  --bmc1_non_equiv_states                 false
% 2.17/0.99  --bmc1_deadlock                         false
% 2.17/0.99  --bmc1_ucm                              false
% 2.17/0.99  --bmc1_add_unsat_core                   none
% 2.17/0.99  --bmc1_unsat_core_children              false
% 2.17/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/0.99  --bmc1_out_stat                         full
% 2.17/0.99  --bmc1_ground_init                      false
% 2.17/0.99  --bmc1_pre_inst_next_state              false
% 2.17/0.99  --bmc1_pre_inst_state                   false
% 2.17/0.99  --bmc1_pre_inst_reach_state             false
% 2.17/0.99  --bmc1_out_unsat_core                   false
% 2.17/0.99  --bmc1_aig_witness_out                  false
% 2.17/0.99  --bmc1_verbose                          false
% 2.17/0.99  --bmc1_dump_clauses_tptp                false
% 2.17/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.17/0.99  --bmc1_dump_file                        -
% 2.17/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.17/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.17/0.99  --bmc1_ucm_extend_mode                  1
% 2.17/0.99  --bmc1_ucm_init_mode                    2
% 2.17/0.99  --bmc1_ucm_cone_mode                    none
% 2.17/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.17/0.99  --bmc1_ucm_relax_model                  4
% 2.17/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.17/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/0.99  --bmc1_ucm_layered_model                none
% 2.17/0.99  --bmc1_ucm_max_lemma_size               10
% 2.17/0.99  
% 2.17/0.99  ------ AIG Options
% 2.17/0.99  
% 2.17/0.99  --aig_mode                              false
% 2.17/0.99  
% 2.17/0.99  ------ Instantiation Options
% 2.17/0.99  
% 2.17/0.99  --instantiation_flag                    true
% 2.17/0.99  --inst_sos_flag                         false
% 2.17/0.99  --inst_sos_phase                        true
% 2.17/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/0.99  --inst_lit_sel_side                     none
% 2.17/0.99  --inst_solver_per_active                1400
% 2.17/0.99  --inst_solver_calls_frac                1.
% 2.17/0.99  --inst_passive_queue_type               priority_queues
% 2.17/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/0.99  --inst_passive_queues_freq              [25;2]
% 2.17/0.99  --inst_dismatching                      true
% 2.17/0.99  --inst_eager_unprocessed_to_passive     true
% 2.17/0.99  --inst_prop_sim_given                   true
% 2.17/0.99  --inst_prop_sim_new                     false
% 2.17/0.99  --inst_subs_new                         false
% 2.17/0.99  --inst_eq_res_simp                      false
% 2.17/0.99  --inst_subs_given                       false
% 2.17/0.99  --inst_orphan_elimination               true
% 2.17/0.99  --inst_learning_loop_flag               true
% 2.17/0.99  --inst_learning_start                   3000
% 2.17/0.99  --inst_learning_factor                  2
% 2.17/0.99  --inst_start_prop_sim_after_learn       3
% 2.17/0.99  --inst_sel_renew                        solver
% 2.17/0.99  --inst_lit_activity_flag                true
% 2.17/0.99  --inst_restr_to_given                   false
% 2.17/0.99  --inst_activity_threshold               500
% 2.17/0.99  --inst_out_proof                        true
% 2.17/0.99  
% 2.17/0.99  ------ Resolution Options
% 2.17/0.99  
% 2.17/0.99  --resolution_flag                       false
% 2.17/0.99  --res_lit_sel                           adaptive
% 2.17/0.99  --res_lit_sel_side                      none
% 2.17/0.99  --res_ordering                          kbo
% 2.17/0.99  --res_to_prop_solver                    active
% 2.17/0.99  --res_prop_simpl_new                    false
% 2.17/0.99  --res_prop_simpl_given                  true
% 2.17/0.99  --res_passive_queue_type                priority_queues
% 2.17/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/0.99  --res_passive_queues_freq               [15;5]
% 2.17/0.99  --res_forward_subs                      full
% 2.17/0.99  --res_backward_subs                     full
% 2.17/0.99  --res_forward_subs_resolution           true
% 2.17/0.99  --res_backward_subs_resolution          true
% 2.17/0.99  --res_orphan_elimination                true
% 2.17/0.99  --res_time_limit                        2.
% 2.17/0.99  --res_out_proof                         true
% 2.17/0.99  
% 2.17/0.99  ------ Superposition Options
% 2.17/0.99  
% 2.17/0.99  --superposition_flag                    true
% 2.17/0.99  --sup_passive_queue_type                priority_queues
% 2.17/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.17/0.99  --demod_completeness_check              fast
% 2.17/0.99  --demod_use_ground                      true
% 2.17/0.99  --sup_to_prop_solver                    passive
% 2.17/0.99  --sup_prop_simpl_new                    true
% 2.17/0.99  --sup_prop_simpl_given                  true
% 2.17/0.99  --sup_fun_splitting                     false
% 2.17/0.99  --sup_smt_interval                      50000
% 2.17/0.99  
% 2.17/0.99  ------ Superposition Simplification Setup
% 2.17/0.99  
% 2.17/0.99  --sup_indices_passive                   []
% 2.17/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.99  --sup_full_bw                           [BwDemod]
% 2.17/0.99  --sup_immed_triv                        [TrivRules]
% 2.17/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.99  --sup_immed_bw_main                     []
% 2.17/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/0.99  
% 2.17/0.99  ------ Combination Options
% 2.17/0.99  
% 2.17/0.99  --comb_res_mult                         3
% 2.17/0.99  --comb_sup_mult                         2
% 2.17/0.99  --comb_inst_mult                        10
% 2.17/0.99  
% 2.17/0.99  ------ Debug Options
% 2.17/0.99  
% 2.17/0.99  --dbg_backtrace                         false
% 2.17/0.99  --dbg_dump_prop_clauses                 false
% 2.17/0.99  --dbg_dump_prop_clauses_file            -
% 2.17/0.99  --dbg_out_stat                          false
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  ------ Proving...
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 2.17/0.99  
% 2.17/0.99  % SZS output start Saturation for theBenchmark.p
% 2.17/0.99  
% 2.17/0.99  fof(f12,axiom,(
% 2.17/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f30,plain,(
% 2.17/0.99    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.17/0.99    inference(ennf_transformation,[],[f12])).
% 2.17/0.99  
% 2.17/0.99  fof(f42,plain,(
% 2.17/0.99    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.17/0.99    inference(nnf_transformation,[],[f30])).
% 2.17/0.99  
% 2.17/0.99  fof(f59,plain,(
% 2.17/0.99    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f42])).
% 2.17/0.99  
% 2.17/0.99  fof(f16,axiom,(
% 2.17/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f34,plain,(
% 2.17/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.17/0.99    inference(ennf_transformation,[],[f16])).
% 2.17/0.99  
% 2.17/0.99  fof(f35,plain,(
% 2.17/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.17/0.99    inference(flattening,[],[f34])).
% 2.17/0.99  
% 2.17/0.99  fof(f65,plain,(
% 2.17/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f35])).
% 2.17/0.99  
% 2.17/0.99  fof(f2,axiom,(
% 2.17/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f47,plain,(
% 2.17/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f2])).
% 2.17/0.99  
% 2.17/0.99  fof(f3,axiom,(
% 2.17/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f48,plain,(
% 2.17/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f3])).
% 2.17/0.99  
% 2.17/0.99  fof(f4,axiom,(
% 2.17/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f49,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f4])).
% 2.17/0.99  
% 2.17/0.99  fof(f73,plain,(
% 2.17/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.17/0.99    inference(definition_unfolding,[],[f48,f49])).
% 2.17/0.99  
% 2.17/0.99  fof(f74,plain,(
% 2.17/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.17/0.99    inference(definition_unfolding,[],[f47,f73])).
% 2.17/0.99  
% 2.17/0.99  fof(f76,plain,(
% 2.17/0.99    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.17/0.99    inference(definition_unfolding,[],[f65,f74])).
% 2.17/0.99  
% 2.17/0.99  fof(f20,conjecture,(
% 2.17/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f21,negated_conjecture,(
% 2.17/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.17/0.99    inference(negated_conjecture,[],[f20])).
% 2.17/0.99  
% 2.17/0.99  fof(f22,plain,(
% 2.17/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.17/0.99    inference(pure_predicate_removal,[],[f21])).
% 2.17/0.99  
% 2.17/0.99  fof(f39,plain,(
% 2.17/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.17/0.99    inference(ennf_transformation,[],[f22])).
% 2.17/0.99  
% 2.17/0.99  fof(f40,plain,(
% 2.17/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.17/0.99    inference(flattening,[],[f39])).
% 2.17/0.99  
% 2.17/0.99  fof(f44,plain,(
% 2.17/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.17/0.99    introduced(choice_axiom,[])).
% 2.17/0.99  
% 2.17/0.99  fof(f45,plain,(
% 2.17/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44])).
% 2.17/0.99  
% 2.17/0.99  fof(f69,plain,(
% 2.17/0.99    v1_funct_1(sK3)),
% 2.17/0.99    inference(cnf_transformation,[],[f45])).
% 2.17/0.99  
% 2.17/0.99  fof(f70,plain,(
% 2.17/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.17/0.99    inference(cnf_transformation,[],[f45])).
% 2.17/0.99  
% 2.17/0.99  fof(f78,plain,(
% 2.17/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.17/0.99    inference(definition_unfolding,[],[f70,f74])).
% 2.17/0.99  
% 2.17/0.99  fof(f17,axiom,(
% 2.17/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f36,plain,(
% 2.17/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.99    inference(ennf_transformation,[],[f17])).
% 2.17/0.99  
% 2.17/0.99  fof(f66,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.17/0.99    inference(cnf_transformation,[],[f36])).
% 2.17/0.99  
% 2.17/0.99  fof(f19,axiom,(
% 2.17/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f38,plain,(
% 2.17/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.99    inference(ennf_transformation,[],[f19])).
% 2.17/0.99  
% 2.17/0.99  fof(f68,plain,(
% 2.17/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.17/0.99    inference(cnf_transformation,[],[f38])).
% 2.17/0.99  
% 2.17/0.99  fof(f9,axiom,(
% 2.17/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f28,plain,(
% 2.17/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.17/0.99    inference(ennf_transformation,[],[f9])).
% 2.17/0.99  
% 2.17/0.99  fof(f54,plain,(
% 2.17/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f28])).
% 2.17/0.99  
% 2.17/0.99  fof(f8,axiom,(
% 2.17/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f27,plain,(
% 2.17/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.17/0.99    inference(ennf_transformation,[],[f8])).
% 2.17/0.99  
% 2.17/0.99  fof(f53,plain,(
% 2.17/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f27])).
% 2.17/0.99  
% 2.17/0.99  fof(f72,plain,(
% 2.17/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.17/0.99    inference(cnf_transformation,[],[f45])).
% 2.17/0.99  
% 2.17/0.99  fof(f77,plain,(
% 2.17/0.99    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.17/0.99    inference(definition_unfolding,[],[f72,f74,f74])).
% 2.17/0.99  
% 2.17/0.99  fof(f18,axiom,(
% 2.17/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f23,plain,(
% 2.17/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.17/0.99    inference(pure_predicate_removal,[],[f18])).
% 2.17/0.99  
% 2.17/0.99  fof(f37,plain,(
% 2.17/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.99    inference(ennf_transformation,[],[f23])).
% 2.17/0.99  
% 2.17/0.99  fof(f67,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.17/0.99    inference(cnf_transformation,[],[f37])).
% 2.17/0.99  
% 2.17/0.99  fof(f13,axiom,(
% 2.17/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f31,plain,(
% 2.17/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.17/0.99    inference(ennf_transformation,[],[f13])).
% 2.17/0.99  
% 2.17/0.99  fof(f32,plain,(
% 2.17/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.17/0.99    inference(flattening,[],[f31])).
% 2.17/0.99  
% 2.17/0.99  fof(f60,plain,(
% 2.17/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f32])).
% 2.17/0.99  
% 2.17/0.99  fof(f7,axiom,(
% 2.17/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f26,plain,(
% 2.17/0.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.17/0.99    inference(ennf_transformation,[],[f7])).
% 2.17/0.99  
% 2.17/0.99  fof(f52,plain,(
% 2.17/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f26])).
% 2.17/0.99  
% 2.17/0.99  fof(f75,plain,(
% 2.17/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.17/0.99    inference(definition_unfolding,[],[f52,f74])).
% 2.17/0.99  
% 2.17/0.99  fof(f15,axiom,(
% 2.17/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f33,plain,(
% 2.17/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.17/0.99    inference(ennf_transformation,[],[f15])).
% 2.17/0.99  
% 2.17/0.99  fof(f43,plain,(
% 2.17/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.17/0.99    inference(nnf_transformation,[],[f33])).
% 2.17/0.99  
% 2.17/0.99  fof(f64,plain,(
% 2.17/0.99    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f43])).
% 2.17/0.99  
% 2.17/0.99  fof(f5,axiom,(
% 2.17/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f50,plain,(
% 2.17/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.17/0.99    inference(cnf_transformation,[],[f5])).
% 2.17/0.99  
% 2.17/0.99  fof(f10,axiom,(
% 2.17/0.99    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f55,plain,(
% 2.17/0.99    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f10])).
% 2.17/0.99  
% 2.17/0.99  fof(f58,plain,(
% 2.17/0.99    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f42])).
% 2.17/0.99  
% 2.17/0.99  fof(f14,axiom,(
% 2.17/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f61,plain,(
% 2.17/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.17/0.99    inference(cnf_transformation,[],[f14])).
% 2.17/0.99  
% 2.17/0.99  fof(f6,axiom,(
% 2.17/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f24,plain,(
% 2.17/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.17/0.99    inference(ennf_transformation,[],[f6])).
% 2.17/0.99  
% 2.17/0.99  fof(f25,plain,(
% 2.17/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.17/0.99    inference(flattening,[],[f24])).
% 2.17/0.99  
% 2.17/0.99  fof(f51,plain,(
% 2.17/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f25])).
% 2.17/0.99  
% 2.17/0.99  fof(f1,axiom,(
% 2.17/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.17/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/0.99  
% 2.17/0.99  fof(f46,plain,(
% 2.17/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f1])).
% 2.17/0.99  
% 2.17/0.99  fof(f63,plain,(
% 2.17/0.99    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.99    inference(cnf_transformation,[],[f43])).
% 2.17/0.99  
% 2.17/0.99  fof(f71,plain,(
% 2.17/0.99    k1_xboole_0 != sK1),
% 2.17/0.99    inference(cnf_transformation,[],[f45])).
% 2.17/0.99  
% 2.17/0.99  fof(f62,plain,(
% 2.17/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.17/0.99    inference(cnf_transformation,[],[f14])).
% 2.17/0.99  
% 2.17/0.99  cnf(c_218,plain,
% 2.17/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 2.17/0.99      theory(equality) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_216,plain,
% 2.17/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 2.17/0.99      theory(equality) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_208,plain,
% 2.17/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.17/0.99      theory(equality) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_745,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_9,plain,
% 2.17/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 2.17/0.99      | ~ v1_relat_1(X1)
% 2.17/0.99      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 2.17/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1028,plain,
% 2.17/0.99      ( k11_relat_1(X0,X1) = k1_xboole_0
% 2.17/0.99      | r2_hidden(X1,k1_relat_1(X0)) = iProver_top
% 2.17/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_16,plain,
% 2.17/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.17/0.99      | ~ v1_funct_1(X1)
% 2.17/0.99      | ~ v1_relat_1(X1)
% 2.17/0.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 2.17/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_23,negated_conjecture,
% 2.17/0.99      ( v1_funct_1(sK3) ),
% 2.17/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_285,plain,
% 2.17/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.17/0.99      | ~ v1_relat_1(X1)
% 2.17/0.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 2.17/0.99      | sK3 != X1 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_286,plain,
% 2.17/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.17/0.99      | ~ v1_relat_1(sK3)
% 2.17/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_285]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1019,plain,
% 2.17/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.17/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.17/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_22,negated_conjecture,
% 2.17/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.17/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_25,plain,
% 2.17/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_287,plain,
% 2.17/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.17/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.17/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_286]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_17,plain,
% 2.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.17/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1150,plain,
% 2.17/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.17/0.99      | v1_relat_1(sK3) ),
% 2.17/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1151,plain,
% 2.17/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 2.17/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_1150]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1156,plain,
% 2.17/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 2.17/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_1019,c_25,c_287,c_1151]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1157,plain,
% 2.17/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.17/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 2.17/0.99      inference(renaming,[status(thm)],[c_1156]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2193,plain,
% 2.17/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.17/0.99      | k11_relat_1(sK3,X0) = k1_xboole_0
% 2.17/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1028,c_1157]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2200,plain,
% 2.17/0.99      ( ~ v1_relat_1(sK3)
% 2.17/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.17/0.99      | k11_relat_1(sK3,X0) = k1_xboole_0 ),
% 2.17/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2193]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2368,plain,
% 2.17/0.99      ( k11_relat_1(sK3,X0) = k1_xboole_0
% 2.17/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_2193,c_22,c_1150,c_2200]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2369,plain,
% 2.17/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.17/0.99      | k11_relat_1(sK3,X0) = k1_xboole_0 ),
% 2.17/0.99      inference(renaming,[status(thm)],[c_2368]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1022,plain,
% 2.17/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_19,plain,
% 2.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.17/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1023,plain,
% 2.17/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.17/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1633,plain,
% 2.17/0.99      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1022,c_1023]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1024,plain,
% 2.17/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.17/0.99      | v1_relat_1(X0) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1318,plain,
% 2.17/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1022,c_1024]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_5,plain,
% 2.17/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.17/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1029,plain,
% 2.17/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.17/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1374,plain,
% 2.17/0.99      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1318,c_1029]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_4,plain,
% 2.17/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.17/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_20,negated_conjecture,
% 2.17/0.99      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.17/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_246,plain,
% 2.17/0.99      ( ~ v1_relat_1(X0)
% 2.17/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(X0,X1)
% 2.17/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(X0) ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_20]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1021,plain,
% 2.17/0.99      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(X0,X1)
% 2.17/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(X0)
% 2.17/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1424,plain,
% 2.17/0.99      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(k7_relat_1(sK3,X0),X1)
% 2.17/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k9_relat_1(sK3,X0)
% 2.17/0.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1374,c_1021]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1804,plain,
% 2.17/0.99      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k9_relat_1(sK3,X0)
% 2.17/0.99      | k9_relat_1(k7_relat_1(sK3,X0),X1) != k9_relat_1(sK3,sK2)
% 2.17/0.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_1633,c_1424]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2373,plain,
% 2.17/0.99      ( k9_relat_1(k7_relat_1(sK3,X0),X1) != k9_relat_1(sK3,sK2)
% 2.17/0.99      | k9_relat_1(sK3,X0) != k11_relat_1(sK3,sK0)
% 2.17/0.99      | k11_relat_1(sK3,sK0) = k1_xboole_0
% 2.17/0.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_2369,c_1804]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_18,plain,
% 2.17/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.17/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_11,plain,
% 2.17/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.17/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_265,plain,
% 2.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.99      | ~ v1_relat_1(X0)
% 2.17/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.17/0.99      inference(resolution,[status(thm)],[c_18,c_11]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_269,plain,
% 2.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.17/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_265,c_18,c_17,c_11]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1020,plain,
% 2.17/0.99      ( k7_relat_1(X0,X1) = X0
% 2.17/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1254,plain,
% 2.17/0.99      ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = sK3 ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1022,c_1020]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1423,plain,
% 2.17/0.99      ( k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(sK3) ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1254,c_1374]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_3,plain,
% 2.17/0.99      ( ~ v1_relat_1(X0)
% 2.17/0.99      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.17/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1030,plain,
% 2.17/0.99      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.17/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1741,plain,
% 2.17/0.99      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1318,c_1030]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1887,plain,
% 2.17/0.99      ( k11_relat_1(sK3,sK0) = k2_relat_1(sK3) ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1423,c_1741]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2394,plain,
% 2.17/0.99      ( k9_relat_1(k7_relat_1(sK3,X0),X1) != k9_relat_1(sK3,sK2)
% 2.17/0.99      | k9_relat_1(sK3,X0) != k2_relat_1(sK3)
% 2.17/0.99      | k11_relat_1(sK3,sK0) = k1_xboole_0
% 2.17/0.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 2.17/0.99      inference(light_normalisation,[status(thm)],[c_2373,c_1887]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2395,plain,
% 2.17/0.99      ( k9_relat_1(k7_relat_1(sK3,X0),X1) != k9_relat_1(sK3,sK2)
% 2.17/0.99      | k9_relat_1(sK3,X0) != k2_relat_1(sK3)
% 2.17/0.99      | k2_relat_1(sK3) = k1_xboole_0
% 2.17/0.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_2394,c_1887]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1805,plain,
% 2.17/0.99      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(X0)
% 2.17/0.99      | k9_relat_1(X0,X1) != k9_relat_1(sK3,sK2)
% 2.17/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_1633,c_1021]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2374,plain,
% 2.17/0.99      ( k9_relat_1(X0,X1) != k9_relat_1(sK3,sK2)
% 2.17/0.99      | k11_relat_1(sK3,sK0) != k2_relat_1(X0)
% 2.17/0.99      | k11_relat_1(sK3,sK0) = k1_xboole_0
% 2.17/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_2369,c_1805]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2384,plain,
% 2.17/0.99      ( k9_relat_1(X0,X1) != k9_relat_1(sK3,sK2)
% 2.17/0.99      | k11_relat_1(sK3,sK0) = k1_xboole_0
% 2.17/0.99      | k2_relat_1(X0) != k2_relat_1(sK3)
% 2.17/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.17/0.99      inference(light_normalisation,[status(thm)],[c_2374,c_1887]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2385,plain,
% 2.17/0.99      ( k9_relat_1(X0,X1) != k9_relat_1(sK3,sK2)
% 2.17/0.99      | k2_relat_1(X0) != k2_relat_1(sK3)
% 2.17/0.99      | k2_relat_1(sK3) = k1_xboole_0
% 2.17/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_2384,c_1887]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2593,plain,
% 2.17/0.99      ( k2_relat_1(sK3) != k2_relat_1(sK3)
% 2.17/0.99      | k2_relat_1(sK3) = k1_xboole_0
% 2.17/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.17/0.99      inference(equality_resolution,[status(thm)],[c_2385]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2594,plain,
% 2.17/0.99      ( k2_relat_1(sK3) = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.17/0.99      inference(equality_resolution_simp,[status(thm)],[c_2593]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2704,plain,
% 2.17/0.99      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_2395,c_25,c_1151,c_2594]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_14,plain,
% 2.17/0.99      ( ~ v1_relat_1(X0)
% 2.17/0.99      | k1_relat_1(X0) = k1_xboole_0
% 2.17/0.99      | k2_relat_1(X0) != k1_xboole_0 ),
% 2.17/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1026,plain,
% 2.17/0.99      ( k1_relat_1(X0) = k1_xboole_0
% 2.17/0.99      | k2_relat_1(X0) != k1_xboole_0
% 2.17/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2719,plain,
% 2.17/0.99      ( k1_relat_1(sK3) = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_2704,c_1026]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2262,plain,
% 2.17/0.99      ( ~ v1_relat_1(sK3)
% 2.17/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 2.17/0.99      | k2_relat_1(sK3) != k1_xboole_0 ),
% 2.17/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2825,plain,
% 2.17/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_2719,c_22,c_25,c_1150,c_1151,c_2262,c_2594]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2829,plain,
% 2.17/0.99      ( k11_relat_1(sK3,X0) = k1_xboole_0
% 2.17/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 2.17/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_2825,c_1028]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1142,plain,
% 2.17/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.17/0.99      | v1_relat_1(k1_xboole_0) ),
% 2.17/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1144,plain,
% 2.17/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.17/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_1142]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1,plain,
% 2.17/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.17/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1143,plain,
% 2.17/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.17/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1146,plain,
% 2.17/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_1143]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1032,plain,
% 2.17/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1317,plain,
% 2.17/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1032,c_1024]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1740,plain,
% 2.17/0.99      ( k9_relat_1(k1_xboole_0,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(k1_xboole_0,X0) ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1317,c_1030]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_6,plain,
% 2.17/0.99      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.17/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1745,plain,
% 2.17/0.99      ( k11_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_1740,c_6]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_10,plain,
% 2.17/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.17/0.99      | ~ v1_relat_1(X1)
% 2.17/0.99      | k11_relat_1(X1,X0) != k1_xboole_0 ),
% 2.17/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1027,plain,
% 2.17/0.99      ( k11_relat_1(X0,X1) != k1_xboole_0
% 2.17/0.99      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.17/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2115,plain,
% 2.17/0.99      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 2.17/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1745,c_1027]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_13,plain,
% 2.17/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.17/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2118,plain,
% 2.17/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 2.17/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.17/0.99      inference(light_normalisation,[status(thm)],[c_2115,c_13]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2841,plain,
% 2.17/0.99      ( k11_relat_1(sK3,X0) = k1_xboole_0 ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_2829,c_25,c_1144,c_1146,c_1151,c_2118]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1727,plain,
% 2.17/0.99      ( k9_relat_1(sK3,X0) != k1_xboole_0
% 2.17/0.99      | k1_relat_1(k7_relat_1(sK3,X0)) = k1_xboole_0
% 2.17/0.99      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1374,c_1026]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2043,plain,
% 2.17/0.99      ( k11_relat_1(sK3,X0) != k1_xboole_0
% 2.17/0.99      | k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) = k1_xboole_0
% 2.17/0.99      | v1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1741,c_1727]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2849,plain,
% 2.17/0.99      ( k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) = k1_xboole_0
% 2.17/0.99      | k1_xboole_0 != k1_xboole_0
% 2.17/0.99      | v1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_2841,c_2043]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2853,plain,
% 2.17/0.99      ( k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) = k1_xboole_0
% 2.17/0.99      | v1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 2.17/0.99      inference(equality_resolution_simp,[status(thm)],[c_2849]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2850,plain,
% 2.17/0.99      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k1_xboole_0 ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_2841,c_1741]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1965,plain,
% 2.17/0.99      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k11_relat_1(sK3,X0)
% 2.17/0.99      | k9_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)),X1) != k9_relat_1(sK3,sK2)
% 2.17/0.99      | v1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1741,c_1804]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2847,plain,
% 2.17/0.99      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k1_xboole_0
% 2.17/0.99      | k9_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)),X1) != k9_relat_1(sK3,sK2)
% 2.17/0.99      | v1_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))) != iProver_top ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_2841,c_1965]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2710,plain,
% 2.17/0.99      ( k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0 ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_2704,c_1423]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2,plain,
% 2.17/0.99      ( ~ r2_hidden(X0,X1)
% 2.17/0.99      | m1_subset_1(X0,X2)
% 2.17/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.17/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1031,plain,
% 2.17/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.17/0.99      | m1_subset_1(X0,X2) = iProver_top
% 2.17/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2291,plain,
% 2.17/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 2.17/0.99      | m1_subset_1(X0,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1022,c_1031]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_2181,plain,
% 2.17/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.17/0.99      inference(global_propositional_subsumption,
% 2.17/0.99                [status(thm)],
% 2.17/0.99                [c_2118,c_1144,c_1146]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_0,plain,
% 2.17/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.17/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_241,plain,
% 2.17/0.99      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k1_xboole_0
% 2.17/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 2.17/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_242,plain,
% 2.17/0.99      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k1_xboole_0 ),
% 2.17/0.99      inference(unflattening,[status(thm)],[c_241]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1806,plain,
% 2.17/0.99      ( k9_relat_1(sK3,sK2) != k1_xboole_0 ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_1633,c_242]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1632,plain,
% 2.17/0.99      ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1032,c_1023]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1637,plain,
% 2.17/0.99      ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k1_xboole_0 ),
% 2.17/0.99      inference(demodulation,[status(thm)],[c_1632,c_6]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1257,plain,
% 2.17/0.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.17/0.99      inference(superposition,[status(thm)],[c_1032,c_1020]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_15,plain,
% 2.17/0.99      ( ~ v1_relat_1(X0)
% 2.17/0.99      | k1_relat_1(X0) != k1_xboole_0
% 2.17/0.99      | k2_relat_1(X0) = k1_xboole_0 ),
% 2.17/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_1025,plain,
% 2.17/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 2.17/0.99      | k2_relat_1(X0) = k1_xboole_0
% 2.17/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.17/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_21,negated_conjecture,
% 2.17/0.99      ( k1_xboole_0 != sK1 ),
% 2.17/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.17/0.99  
% 2.17/0.99  cnf(c_12,plain,
% 2.17/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.17/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  % SZS output end Saturation for theBenchmark.p
% 2.17/0.99  
% 2.17/0.99  ------                               Statistics
% 2.17/0.99  
% 2.17/0.99  ------ General
% 2.17/0.99  
% 2.17/0.99  abstr_ref_over_cycles:                  0
% 2.17/0.99  abstr_ref_under_cycles:                 0
% 2.17/0.99  gc_basic_clause_elim:                   0
% 2.17/0.99  forced_gc_time:                         0
% 2.17/0.99  parsing_time:                           0.009
% 2.17/0.99  unif_index_cands_time:                  0.
% 2.17/0.99  unif_index_add_time:                    0.
% 2.17/0.99  orderings_time:                         0.
% 2.17/0.99  out_proof_time:                         0.
% 2.17/0.99  total_time:                             0.127
% 2.17/0.99  num_of_symbols:                         53
% 2.17/0.99  num_of_terms:                           2548
% 2.17/0.99  
% 2.17/0.99  ------ Preprocessing
% 2.17/0.99  
% 2.17/0.99  num_of_splits:                          0
% 2.17/0.99  num_of_split_atoms:                     0
% 2.17/0.99  num_of_reused_defs:                     0
% 2.17/0.99  num_eq_ax_congr_red:                    17
% 2.17/0.99  num_of_sem_filtered_clauses:            1
% 2.17/0.99  num_of_subtypes:                        0
% 2.17/0.99  monotx_restored_types:                  0
% 2.17/0.99  sat_num_of_epr_types:                   0
% 2.17/0.99  sat_num_of_non_cyclic_types:            0
% 2.17/0.99  sat_guarded_non_collapsed_types:        0
% 2.17/0.99  num_pure_diseq_elim:                    0
% 2.17/0.99  simp_replaced_by:                       0
% 2.17/0.99  res_preprocessed:                       110
% 2.17/0.99  prep_upred:                             0
% 2.17/0.99  prep_unflattend:                        14
% 2.17/0.99  smt_new_axioms:                         0
% 2.17/0.99  pred_elim_cands:                        3
% 2.17/0.99  pred_elim:                              4
% 2.17/0.99  pred_elim_cl:                           5
% 2.17/0.99  pred_elim_cycles:                       8
% 2.17/0.99  merged_defs:                            0
% 2.17/0.99  merged_defs_ncl:                        0
% 2.17/0.99  bin_hyper_res:                          0
% 2.17/0.99  prep_cycles:                            4
% 2.17/0.99  pred_elim_time:                         0.007
% 2.17/0.99  splitting_time:                         0.
% 2.17/0.99  sem_filter_time:                        0.
% 2.17/0.99  monotx_time:                            0.
% 2.17/0.99  subtype_inf_time:                       0.
% 2.17/0.99  
% 2.17/0.99  ------ Problem properties
% 2.17/0.99  
% 2.17/0.99  clauses:                                19
% 2.17/0.99  conjectures:                            2
% 2.17/0.99  epr:                                    1
% 2.17/0.99  horn:                                   18
% 2.17/0.99  ground:                                 5
% 2.17/0.99  unary:                                  7
% 2.17/0.99  binary:                                 5
% 2.17/0.99  lits:                                   38
% 2.17/0.99  lits_eq:                                18
% 2.17/0.99  fd_pure:                                0
% 2.17/0.99  fd_pseudo:                              0
% 2.17/0.99  fd_cond:                                0
% 2.17/0.99  fd_pseudo_cond:                         0
% 2.17/0.99  ac_symbols:                             0
% 2.17/0.99  
% 2.17/0.99  ------ Propositional Solver
% 2.17/0.99  
% 2.17/0.99  prop_solver_calls:                      29
% 2.17/0.99  prop_fast_solver_calls:                 697
% 2.17/0.99  smt_solver_calls:                       0
% 2.17/0.99  smt_fast_solver_calls:                  0
% 2.17/0.99  prop_num_of_clauses:                    944
% 2.17/0.99  prop_preprocess_simplified:             3882
% 2.17/0.99  prop_fo_subsumed:                       19
% 2.17/0.99  prop_solver_time:                       0.
% 2.17/0.99  smt_solver_time:                        0.
% 2.17/0.99  smt_fast_solver_time:                   0.
% 2.17/0.99  prop_fast_solver_time:                  0.
% 2.17/0.99  prop_unsat_core_time:                   0.
% 2.17/0.99  
% 2.17/0.99  ------ QBF
% 2.17/0.99  
% 2.17/0.99  qbf_q_res:                              0
% 2.17/0.99  qbf_num_tautologies:                    0
% 2.17/0.99  qbf_prep_cycles:                        0
% 2.17/0.99  
% 2.17/0.99  ------ BMC1
% 2.17/0.99  
% 2.17/0.99  bmc1_current_bound:                     -1
% 2.17/0.99  bmc1_last_solved_bound:                 -1
% 2.17/0.99  bmc1_unsat_core_size:                   -1
% 2.17/0.99  bmc1_unsat_core_parents_size:           -1
% 2.17/0.99  bmc1_merge_next_fun:                    0
% 2.17/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.17/0.99  
% 2.17/0.99  ------ Instantiation
% 2.17/0.99  
% 2.17/0.99  inst_num_of_clauses:                    354
% 2.17/0.99  inst_num_in_passive:                    90
% 2.17/0.99  inst_num_in_active:                     224
% 2.17/0.99  inst_num_in_unprocessed:                40
% 2.17/0.99  inst_num_of_loops:                      260
% 2.17/0.99  inst_num_of_learning_restarts:          0
% 2.17/0.99  inst_num_moves_active_passive:          32
% 2.17/0.99  inst_lit_activity:                      0
% 2.17/0.99  inst_lit_activity_moves:                0
% 2.17/0.99  inst_num_tautologies:                   0
% 2.17/0.99  inst_num_prop_implied:                  0
% 2.17/0.99  inst_num_existing_simplified:           0
% 2.17/0.99  inst_num_eq_res_simplified:             0
% 2.17/0.99  inst_num_child_elim:                    0
% 2.17/0.99  inst_num_of_dismatching_blockings:      92
% 2.17/0.99  inst_num_of_non_proper_insts:           337
% 2.17/0.99  inst_num_of_duplicates:                 0
% 2.17/0.99  inst_inst_num_from_inst_to_res:         0
% 2.17/0.99  inst_dismatching_checking_time:         0.
% 2.17/0.99  
% 2.17/0.99  ------ Resolution
% 2.17/0.99  
% 2.17/0.99  res_num_of_clauses:                     0
% 2.17/0.99  res_num_in_passive:                     0
% 2.17/0.99  res_num_in_active:                      0
% 2.17/0.99  res_num_of_loops:                       114
% 2.17/0.99  res_forward_subset_subsumed:            43
% 2.17/0.99  res_backward_subset_subsumed:           0
% 2.17/0.99  res_forward_subsumed:                   0
% 2.17/0.99  res_backward_subsumed:                  0
% 2.17/0.99  res_forward_subsumption_resolution:     0
% 2.17/0.99  res_backward_subsumption_resolution:    0
% 2.17/0.99  res_clause_to_clause_subsumption:       74
% 2.17/0.99  res_orphan_elimination:                 0
% 2.17/0.99  res_tautology_del:                      51
% 2.17/0.99  res_num_eq_res_simplified:              0
% 2.17/0.99  res_num_sel_changes:                    0
% 2.17/0.99  res_moves_from_active_to_pass:          0
% 2.17/0.99  
% 2.17/0.99  ------ Superposition
% 2.17/0.99  
% 2.17/0.99  sup_time_total:                         0.
% 2.17/0.99  sup_time_generating:                    0.
% 2.17/0.99  sup_time_sim_full:                      0.
% 2.17/0.99  sup_time_sim_immed:                     0.
% 2.17/0.99  
% 2.17/0.99  sup_num_of_clauses:                     40
% 2.17/0.99  sup_num_in_active:                      37
% 2.17/0.99  sup_num_in_passive:                     3
% 2.17/0.99  sup_num_of_loops:                       51
% 2.17/0.99  sup_fw_superposition:                   31
% 2.17/0.99  sup_bw_superposition:                   19
% 2.17/0.99  sup_immediate_simplified:               22
% 2.17/0.99  sup_given_eliminated:                   0
% 2.17/0.99  comparisons_done:                       0
% 2.17/0.99  comparisons_avoided:                    3
% 2.17/0.99  
% 2.17/0.99  ------ Simplifications
% 2.17/0.99  
% 2.17/0.99  
% 2.17/0.99  sim_fw_subset_subsumed:                 9
% 2.17/0.99  sim_bw_subset_subsumed:                 2
% 2.17/0.99  sim_fw_subsumed:                        4
% 2.17/0.99  sim_bw_subsumed:                        0
% 2.17/0.99  sim_fw_subsumption_res:                 0
% 2.17/0.99  sim_bw_subsumption_res:                 0
% 2.17/0.99  sim_tautology_del:                      0
% 2.17/0.99  sim_eq_tautology_del:                   6
% 2.17/0.99  sim_eq_res_simp:                        6
% 2.17/0.99  sim_fw_demodulated:                     7
% 2.17/0.99  sim_bw_demodulated:                     14
% 2.17/0.99  sim_light_normalised:                   12
% 2.17/0.99  sim_joinable_taut:                      0
% 2.17/0.99  sim_joinable_simp:                      0
% 2.17/0.99  sim_ac_normalised:                      0
% 2.17/0.99  sim_smt_subsumption:                    0
% 2.17/0.99  
%------------------------------------------------------------------------------
