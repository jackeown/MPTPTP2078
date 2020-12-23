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
% DateTime   : Thu Dec  3 12:04:49 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 365 expanded)
%              Number of clauses        :  102 ( 145 expanded)
%              Number of leaves         :   25 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          :  396 (1064 expanded)
%              Number of equality atoms :  156 ( 305 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f42,plain,
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

fof(f43,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f42])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f64,f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f47])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    v1_funct_2(sK3,k2_tarski(sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f63,f47])).

fof(f65,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f39])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0] : ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f48,f47])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_249,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_250,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_249])).

cnf(c_585,plain,
    ( ~ r2_hidden(X0_51,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_250])).

cnf(c_2186,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_585])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_594,plain,
    ( r2_hidden(X0_51,k1_relat_1(X0_52))
    | ~ v1_relat_1(X0_52)
    | k11_relat_1(X0_52,X0_51) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_918,plain,
    ( k11_relat_1(X0_52,X0_51) = k1_xboole_0
    | r2_hidden(X0_51,k1_relat_1(X0_52)) = iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_301,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_302,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_582,plain,
    ( ~ r2_hidden(X0_51,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0_51),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_302])).

cnf(c_928,plain,
    ( r2_hidden(X0_51,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_51),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_661,plain,
    ( r2_hidden(X0_51,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_51),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1034,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_1035,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_1060,plain,
    ( r2_hidden(k1_funct_1(sK3,X0_51),k2_relat_1(sK3)) = iProver_top
    | r2_hidden(X0_51,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_928,c_24,c_661,c_1035])).

cnf(c_1061,plain,
    ( r2_hidden(X0_51,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_51),k2_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1060])).

cnf(c_587,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_924,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k2_relset_1(X1_52,X2_52,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_922,plain,
    ( k2_relset_1(X0_52,X1_52,X2_52) = k2_relat_1(X2_52)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_1246,plain,
    ( k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_924,c_922])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | m1_subset_1(k2_relset_1(X1_52,X2_52,X0_52),k1_zfmisc_1(X2_52)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_921,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_52,X2_52,X0_52),k1_zfmisc_1(X2_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_591])).

cnf(c_1511,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1246,c_921])).

cnf(c_1687,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1511,c_24])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_597,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ r2_hidden(X0_51,X0_52)
    | r2_hidden(X0_51,X1_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_915,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top
    | r2_hidden(X0_51,X0_52) != iProver_top
    | r2_hidden(X0_51,X1_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_1692,plain,
    ( r2_hidden(X0_51,k2_relat_1(sK3)) != iProver_top
    | r2_hidden(X0_51,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1687,c_915])).

cnf(c_1739,plain,
    ( r2_hidden(X0_51,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0_51),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1061,c_1692])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_589,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_923,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_1835,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1739,c_923])).

cnf(c_1839,plain,
    ( k11_relat_1(sK3,sK1) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_918,c_1835])).

cnf(c_920,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_1165,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_924,c_920])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_tarski(X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_596,plain,
    ( ~ v1_relat_1(X0_52)
    | k9_relat_1(X0_52,k2_tarski(X0_51,X0_51)) = k11_relat_1(X0_52,X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_916,plain,
    ( k9_relat_1(X0_52,k2_tarski(X0_51,X0_51)) = k11_relat_1(X0_52,X0_51)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_1272,plain,
    ( k9_relat_1(sK3,k2_tarski(X0_51,X0_51)) = k11_relat_1(sK3,X0_51) ),
    inference(superposition,[status(thm)],[c_1165,c_916])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_260,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_13,c_9])).

cnf(c_264,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_260,c_13,c_12,c_9])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k7_relat_1(X0_52,X1_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_264])).

cnf(c_926,plain,
    ( k7_relat_1(X0_52,X1_52) = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_1431,plain,
    ( k7_relat_1(sK3,k2_tarski(sK1,sK1)) = sK3 ),
    inference(superposition,[status(thm)],[c_924,c_926])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_595,plain,
    ( ~ v1_relat_1(X0_52)
    | k2_relat_1(k7_relat_1(X0_52,X1_52)) = k9_relat_1(X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_917,plain,
    ( k2_relat_1(k7_relat_1(X0_52,X1_52)) = k9_relat_1(X0_52,X1_52)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_1273,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0_52)) = k9_relat_1(sK3,X0_52) ),
    inference(superposition,[status(thm)],[c_1165,c_917])).

cnf(c_1433,plain,
    ( k9_relat_1(sK3,k2_tarski(sK1,sK1)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1431,c_1273])).

cnf(c_1697,plain,
    ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1272,c_1433])).

cnf(c_1840,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1839,c_1697])).

cnf(c_1932,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1840,c_24,c_1035])).

cnf(c_1940,plain,
    ( k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1932,c_1246])).

cnf(c_600,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_1806,plain,
    ( k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) = k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_604,plain,
    ( ~ r2_hidden(X0_51,X0_52)
    | r2_hidden(X1_51,X1_52)
    | X1_52 != X0_52
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_1449,plain,
    ( r2_hidden(X0_51,X0_52)
    | ~ r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3))
    | X0_52 != k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)
    | X0_51 != k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_1805,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),X0_52)
    | ~ r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3))
    | X0_52 != k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)
    | k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) != k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_1808,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3))
    | r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),k1_xboole_0)
    | k1_xboole_0 != k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)
    | k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) != k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_1805])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,k2_tarski(sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k2_tarski(sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_281,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2)))
    | ~ r2_hidden(X0,k2_tarski(sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_285,plain,
    ( ~ r2_hidden(X0,k2_tarski(sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_281,c_21,c_19,c_18])).

cnf(c_583,plain,
    ( ~ r2_hidden(X0_51,k2_tarski(sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0_51),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_285])).

cnf(c_1400,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3))
    | ~ r2_hidden(sK0(k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_603,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_1373,plain,
    ( X0_52 != X1_52
    | X0_52 = k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)
    | k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3) != X1_52 ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_1374,plain,
    ( k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3) != k1_xboole_0
    | k1_xboole_0 = k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1373])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_598,plain,
    ( r2_hidden(sK0(X0_52),X0_52)
    | k1_xboole_0 = X0_52 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1286,plain,
    ( r2_hidden(sK0(k2_tarski(X0_51,X0_51)),k2_tarski(X0_51,X0_51))
    | k1_xboole_0 = k2_tarski(X0_51,X0_51) ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_1288,plain,
    ( r2_hidden(sK0(k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1286])).

cnf(c_1045,plain,
    ( k2_tarski(X0_51,X0_51) != X0_52
    | k2_tarski(X0_51,X0_51) = k1_xboole_0
    | k1_xboole_0 != X0_52 ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_1133,plain,
    ( k2_tarski(X0_51,X0_51) != k2_tarski(X0_51,X0_51)
    | k2_tarski(X0_51,X0_51) = k1_xboole_0
    | k1_xboole_0 != k2_tarski(X0_51,X0_51) ),
    inference(instantiation,[status(thm)],[c_1045])).

cnf(c_1135,plain,
    ( k2_tarski(sK1,sK1) != k2_tarski(sK1,sK1)
    | k2_tarski(sK1,sK1) = k1_xboole_0
    | k1_xboole_0 != k2_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_243,plain,
    ( k2_tarski(X0,X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_3])).

cnf(c_586,plain,
    ( k2_tarski(X0_51,X0_51) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_243])).

cnf(c_651,plain,
    ( k2_tarski(sK1,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_601,plain,
    ( X0_52 = X0_52 ),
    theory(equality)).

cnf(c_628,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_627,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_605,plain,
    ( k2_tarski(X0_51,X1_51) = k2_tarski(X2_51,X3_51)
    | X0_51 != X2_51
    | X1_51 != X3_51 ),
    theory(equality)).

cnf(c_616,plain,
    ( k2_tarski(sK1,sK1) = k2_tarski(sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2186,c_1940,c_1806,c_1808,c_1400,c_1374,c_1288,c_1135,c_651,c_628,c_627,c_616])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.25/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/0.98  
% 2.25/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.25/0.98  
% 2.25/0.98  ------  iProver source info
% 2.25/0.98  
% 2.25/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.25/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.25/0.98  git: non_committed_changes: false
% 2.25/0.98  git: last_make_outside_of_git: false
% 2.25/0.98  
% 2.25/0.98  ------ 
% 2.25/0.98  
% 2.25/0.98  ------ Input Options
% 2.25/0.98  
% 2.25/0.98  --out_options                           all
% 2.25/0.98  --tptp_safe_out                         true
% 2.25/0.98  --problem_path                          ""
% 2.25/0.98  --include_path                          ""
% 2.25/0.98  --clausifier                            res/vclausify_rel
% 2.25/0.98  --clausifier_options                    --mode clausify
% 2.25/0.98  --stdin                                 false
% 2.25/0.98  --stats_out                             all
% 2.25/0.98  
% 2.25/0.98  ------ General Options
% 2.25/0.98  
% 2.25/0.98  --fof                                   false
% 2.25/0.98  --time_out_real                         305.
% 2.25/0.98  --time_out_virtual                      -1.
% 2.25/0.98  --symbol_type_check                     false
% 2.25/0.98  --clausify_out                          false
% 2.25/0.98  --sig_cnt_out                           false
% 2.25/0.98  --trig_cnt_out                          false
% 2.25/0.98  --trig_cnt_out_tolerance                1.
% 2.25/0.98  --trig_cnt_out_sk_spl                   false
% 2.25/0.98  --abstr_cl_out                          false
% 2.25/0.98  
% 2.25/0.98  ------ Global Options
% 2.25/0.98  
% 2.25/0.98  --schedule                              default
% 2.25/0.98  --add_important_lit                     false
% 2.25/0.98  --prop_solver_per_cl                    1000
% 2.25/0.98  --min_unsat_core                        false
% 2.25/0.98  --soft_assumptions                      false
% 2.25/0.98  --soft_lemma_size                       3
% 2.25/0.98  --prop_impl_unit_size                   0
% 2.25/0.98  --prop_impl_unit                        []
% 2.25/0.98  --share_sel_clauses                     true
% 2.25/0.98  --reset_solvers                         false
% 2.25/0.98  --bc_imp_inh                            [conj_cone]
% 2.25/0.98  --conj_cone_tolerance                   3.
% 2.25/0.98  --extra_neg_conj                        none
% 2.25/0.98  --large_theory_mode                     true
% 2.25/0.98  --prolific_symb_bound                   200
% 2.25/0.98  --lt_threshold                          2000
% 2.25/0.98  --clause_weak_htbl                      true
% 2.25/0.98  --gc_record_bc_elim                     false
% 2.25/0.98  
% 2.25/0.98  ------ Preprocessing Options
% 2.25/0.98  
% 2.25/0.98  --preprocessing_flag                    true
% 2.25/0.98  --time_out_prep_mult                    0.1
% 2.25/0.98  --splitting_mode                        input
% 2.25/0.98  --splitting_grd                         true
% 2.25/0.98  --splitting_cvd                         false
% 2.25/0.98  --splitting_cvd_svl                     false
% 2.25/0.98  --splitting_nvd                         32
% 2.25/0.98  --sub_typing                            true
% 2.25/0.98  --prep_gs_sim                           true
% 2.25/0.98  --prep_unflatten                        true
% 2.25/0.98  --prep_res_sim                          true
% 2.25/0.98  --prep_upred                            true
% 2.25/0.98  --prep_sem_filter                       exhaustive
% 2.25/0.98  --prep_sem_filter_out                   false
% 2.25/0.98  --pred_elim                             true
% 2.25/0.98  --res_sim_input                         true
% 2.25/0.98  --eq_ax_congr_red                       true
% 2.25/0.98  --pure_diseq_elim                       true
% 2.25/0.98  --brand_transform                       false
% 2.25/0.98  --non_eq_to_eq                          false
% 2.25/0.98  --prep_def_merge                        true
% 2.25/0.98  --prep_def_merge_prop_impl              false
% 2.25/0.98  --prep_def_merge_mbd                    true
% 2.25/0.98  --prep_def_merge_tr_red                 false
% 2.25/0.98  --prep_def_merge_tr_cl                  false
% 2.25/0.98  --smt_preprocessing                     true
% 2.25/0.98  --smt_ac_axioms                         fast
% 2.25/0.98  --preprocessed_out                      false
% 2.25/0.98  --preprocessed_stats                    false
% 2.25/0.98  
% 2.25/0.98  ------ Abstraction refinement Options
% 2.25/0.98  
% 2.25/0.98  --abstr_ref                             []
% 2.25/0.98  --abstr_ref_prep                        false
% 2.25/0.98  --abstr_ref_until_sat                   false
% 2.25/0.98  --abstr_ref_sig_restrict                funpre
% 2.25/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.25/0.98  --abstr_ref_under                       []
% 2.25/0.98  
% 2.25/0.98  ------ SAT Options
% 2.25/0.98  
% 2.25/0.98  --sat_mode                              false
% 2.25/0.98  --sat_fm_restart_options                ""
% 2.25/0.98  --sat_gr_def                            false
% 2.25/0.98  --sat_epr_types                         true
% 2.25/0.98  --sat_non_cyclic_types                  false
% 2.25/0.98  --sat_finite_models                     false
% 2.25/0.98  --sat_fm_lemmas                         false
% 2.25/0.98  --sat_fm_prep                           false
% 2.25/0.98  --sat_fm_uc_incr                        true
% 2.25/0.98  --sat_out_model                         small
% 2.25/0.98  --sat_out_clauses                       false
% 2.25/0.98  
% 2.25/0.98  ------ QBF Options
% 2.25/0.98  
% 2.25/0.98  --qbf_mode                              false
% 2.25/0.98  --qbf_elim_univ                         false
% 2.25/0.98  --qbf_dom_inst                          none
% 2.25/0.98  --qbf_dom_pre_inst                      false
% 2.25/0.98  --qbf_sk_in                             false
% 2.25/0.98  --qbf_pred_elim                         true
% 2.25/0.98  --qbf_split                             512
% 2.25/0.98  
% 2.25/0.98  ------ BMC1 Options
% 2.25/0.98  
% 2.25/0.98  --bmc1_incremental                      false
% 2.25/0.98  --bmc1_axioms                           reachable_all
% 2.25/0.98  --bmc1_min_bound                        0
% 2.25/0.98  --bmc1_max_bound                        -1
% 2.25/0.98  --bmc1_max_bound_default                -1
% 2.25/0.98  --bmc1_symbol_reachability              true
% 2.25/0.98  --bmc1_property_lemmas                  false
% 2.25/0.98  --bmc1_k_induction                      false
% 2.25/0.98  --bmc1_non_equiv_states                 false
% 2.25/0.98  --bmc1_deadlock                         false
% 2.25/0.98  --bmc1_ucm                              false
% 2.25/0.98  --bmc1_add_unsat_core                   none
% 2.25/0.98  --bmc1_unsat_core_children              false
% 2.25/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.25/0.98  --bmc1_out_stat                         full
% 2.25/0.98  --bmc1_ground_init                      false
% 2.25/0.98  --bmc1_pre_inst_next_state              false
% 2.25/0.98  --bmc1_pre_inst_state                   false
% 2.25/0.98  --bmc1_pre_inst_reach_state             false
% 2.25/0.98  --bmc1_out_unsat_core                   false
% 2.25/0.98  --bmc1_aig_witness_out                  false
% 2.25/0.98  --bmc1_verbose                          false
% 2.25/0.98  --bmc1_dump_clauses_tptp                false
% 2.25/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.25/0.98  --bmc1_dump_file                        -
% 2.25/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.25/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.25/0.98  --bmc1_ucm_extend_mode                  1
% 2.25/0.98  --bmc1_ucm_init_mode                    2
% 2.25/0.98  --bmc1_ucm_cone_mode                    none
% 2.25/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.25/0.98  --bmc1_ucm_relax_model                  4
% 2.25/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.25/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.25/0.98  --bmc1_ucm_layered_model                none
% 2.25/0.98  --bmc1_ucm_max_lemma_size               10
% 2.25/0.98  
% 2.25/0.98  ------ AIG Options
% 2.25/0.98  
% 2.25/0.98  --aig_mode                              false
% 2.25/0.98  
% 2.25/0.98  ------ Instantiation Options
% 2.25/0.98  
% 2.25/0.98  --instantiation_flag                    true
% 2.25/0.98  --inst_sos_flag                         false
% 2.25/0.98  --inst_sos_phase                        true
% 2.25/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.25/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.25/0.98  --inst_lit_sel_side                     num_symb
% 2.25/0.98  --inst_solver_per_active                1400
% 2.25/0.98  --inst_solver_calls_frac                1.
% 2.25/0.98  --inst_passive_queue_type               priority_queues
% 2.25/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.25/0.98  --inst_passive_queues_freq              [25;2]
% 2.25/0.98  --inst_dismatching                      true
% 2.25/0.98  --inst_eager_unprocessed_to_passive     true
% 2.25/0.98  --inst_prop_sim_given                   true
% 2.25/0.98  --inst_prop_sim_new                     false
% 2.25/0.98  --inst_subs_new                         false
% 2.25/0.98  --inst_eq_res_simp                      false
% 2.25/0.98  --inst_subs_given                       false
% 2.25/0.98  --inst_orphan_elimination               true
% 2.25/0.98  --inst_learning_loop_flag               true
% 2.25/0.98  --inst_learning_start                   3000
% 2.25/0.98  --inst_learning_factor                  2
% 2.25/0.98  --inst_start_prop_sim_after_learn       3
% 2.25/0.98  --inst_sel_renew                        solver
% 2.25/0.98  --inst_lit_activity_flag                true
% 2.25/0.98  --inst_restr_to_given                   false
% 2.25/0.98  --inst_activity_threshold               500
% 2.25/0.98  --inst_out_proof                        true
% 2.25/0.98  
% 2.25/0.98  ------ Resolution Options
% 2.25/0.98  
% 2.25/0.98  --resolution_flag                       true
% 2.25/0.98  --res_lit_sel                           adaptive
% 2.25/0.98  --res_lit_sel_side                      none
% 2.25/0.98  --res_ordering                          kbo
% 2.25/0.98  --res_to_prop_solver                    active
% 2.25/0.98  --res_prop_simpl_new                    false
% 2.25/0.98  --res_prop_simpl_given                  true
% 2.25/0.98  --res_passive_queue_type                priority_queues
% 2.25/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.25/0.98  --res_passive_queues_freq               [15;5]
% 2.25/0.98  --res_forward_subs                      full
% 2.25/0.98  --res_backward_subs                     full
% 2.25/0.98  --res_forward_subs_resolution           true
% 2.25/0.98  --res_backward_subs_resolution          true
% 2.25/0.98  --res_orphan_elimination                true
% 2.25/0.98  --res_time_limit                        2.
% 2.25/0.98  --res_out_proof                         true
% 2.25/0.98  
% 2.25/0.98  ------ Superposition Options
% 2.25/0.98  
% 2.25/0.98  --superposition_flag                    true
% 2.25/0.98  --sup_passive_queue_type                priority_queues
% 2.25/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.25/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.25/0.98  --demod_completeness_check              fast
% 2.25/0.98  --demod_use_ground                      true
% 2.25/0.98  --sup_to_prop_solver                    passive
% 2.25/0.98  --sup_prop_simpl_new                    true
% 2.25/0.98  --sup_prop_simpl_given                  true
% 2.25/0.98  --sup_fun_splitting                     false
% 2.25/0.98  --sup_smt_interval                      50000
% 2.25/0.98  
% 2.25/0.98  ------ Superposition Simplification Setup
% 2.25/0.98  
% 2.25/0.98  --sup_indices_passive                   []
% 2.25/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.25/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.98  --sup_full_bw                           [BwDemod]
% 2.25/0.98  --sup_immed_triv                        [TrivRules]
% 2.25/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.98  --sup_immed_bw_main                     []
% 2.25/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.25/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.98  
% 2.25/0.98  ------ Combination Options
% 2.25/0.98  
% 2.25/0.98  --comb_res_mult                         3
% 2.25/0.98  --comb_sup_mult                         2
% 2.25/0.98  --comb_inst_mult                        10
% 2.25/0.98  
% 2.25/0.98  ------ Debug Options
% 2.25/0.98  
% 2.25/0.98  --dbg_backtrace                         false
% 2.25/0.98  --dbg_dump_prop_clauses                 false
% 2.25/0.98  --dbg_dump_prop_clauses_file            -
% 2.25/0.98  --dbg_out_stat                          false
% 2.25/0.98  ------ Parsing...
% 2.25/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.25/0.98  
% 2.25/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.25/0.98  
% 2.25/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.25/0.98  
% 2.25/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.25/0.98  ------ Proving...
% 2.25/0.98  ------ Problem Properties 
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  clauses                                 17
% 2.25/0.98  conjectures                             3
% 2.25/0.98  EPR                                     2
% 2.25/0.98  Horn                                    15
% 2.25/0.98  unary                                   5
% 2.25/0.98  binary                                  8
% 2.25/0.98  lits                                    33
% 2.25/0.98  lits eq                                 9
% 2.25/0.98  fd_pure                                 0
% 2.25/0.98  fd_pseudo                               0
% 2.25/0.98  fd_cond                                 1
% 2.25/0.98  fd_pseudo_cond                          0
% 2.25/0.98  AC symbols                              0
% 2.25/0.98  
% 2.25/0.98  ------ Schedule dynamic 5 is on 
% 2.25/0.98  
% 2.25/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  ------ 
% 2.25/0.98  Current options:
% 2.25/0.98  ------ 
% 2.25/0.98  
% 2.25/0.98  ------ Input Options
% 2.25/0.98  
% 2.25/0.98  --out_options                           all
% 2.25/0.98  --tptp_safe_out                         true
% 2.25/0.98  --problem_path                          ""
% 2.25/0.98  --include_path                          ""
% 2.25/0.98  --clausifier                            res/vclausify_rel
% 2.25/0.98  --clausifier_options                    --mode clausify
% 2.25/0.98  --stdin                                 false
% 2.25/0.98  --stats_out                             all
% 2.25/0.98  
% 2.25/0.98  ------ General Options
% 2.25/0.98  
% 2.25/0.98  --fof                                   false
% 2.25/0.98  --time_out_real                         305.
% 2.25/0.98  --time_out_virtual                      -1.
% 2.25/0.98  --symbol_type_check                     false
% 2.25/0.98  --clausify_out                          false
% 2.25/0.98  --sig_cnt_out                           false
% 2.25/0.98  --trig_cnt_out                          false
% 2.25/0.98  --trig_cnt_out_tolerance                1.
% 2.25/0.98  --trig_cnt_out_sk_spl                   false
% 2.25/0.98  --abstr_cl_out                          false
% 2.25/0.98  
% 2.25/0.98  ------ Global Options
% 2.25/0.98  
% 2.25/0.98  --schedule                              default
% 2.25/0.98  --add_important_lit                     false
% 2.25/0.98  --prop_solver_per_cl                    1000
% 2.25/0.98  --min_unsat_core                        false
% 2.25/0.98  --soft_assumptions                      false
% 2.25/0.98  --soft_lemma_size                       3
% 2.25/0.98  --prop_impl_unit_size                   0
% 2.25/0.98  --prop_impl_unit                        []
% 2.25/0.98  --share_sel_clauses                     true
% 2.25/0.98  --reset_solvers                         false
% 2.25/0.98  --bc_imp_inh                            [conj_cone]
% 2.25/0.98  --conj_cone_tolerance                   3.
% 2.25/0.98  --extra_neg_conj                        none
% 2.25/0.98  --large_theory_mode                     true
% 2.25/0.98  --prolific_symb_bound                   200
% 2.25/0.98  --lt_threshold                          2000
% 2.25/0.98  --clause_weak_htbl                      true
% 2.25/0.98  --gc_record_bc_elim                     false
% 2.25/0.98  
% 2.25/0.98  ------ Preprocessing Options
% 2.25/0.98  
% 2.25/0.98  --preprocessing_flag                    true
% 2.25/0.98  --time_out_prep_mult                    0.1
% 2.25/0.98  --splitting_mode                        input
% 2.25/0.98  --splitting_grd                         true
% 2.25/0.98  --splitting_cvd                         false
% 2.25/0.98  --splitting_cvd_svl                     false
% 2.25/0.98  --splitting_nvd                         32
% 2.25/0.98  --sub_typing                            true
% 2.25/0.98  --prep_gs_sim                           true
% 2.25/0.98  --prep_unflatten                        true
% 2.25/0.98  --prep_res_sim                          true
% 2.25/0.98  --prep_upred                            true
% 2.25/0.98  --prep_sem_filter                       exhaustive
% 2.25/0.98  --prep_sem_filter_out                   false
% 2.25/0.98  --pred_elim                             true
% 2.25/0.98  --res_sim_input                         true
% 2.25/0.98  --eq_ax_congr_red                       true
% 2.25/0.98  --pure_diseq_elim                       true
% 2.25/0.98  --brand_transform                       false
% 2.25/0.98  --non_eq_to_eq                          false
% 2.25/0.98  --prep_def_merge                        true
% 2.25/0.98  --prep_def_merge_prop_impl              false
% 2.25/0.98  --prep_def_merge_mbd                    true
% 2.25/0.98  --prep_def_merge_tr_red                 false
% 2.25/0.98  --prep_def_merge_tr_cl                  false
% 2.25/0.98  --smt_preprocessing                     true
% 2.25/0.98  --smt_ac_axioms                         fast
% 2.25/0.98  --preprocessed_out                      false
% 2.25/0.98  --preprocessed_stats                    false
% 2.25/0.98  
% 2.25/0.98  ------ Abstraction refinement Options
% 2.25/0.98  
% 2.25/0.98  --abstr_ref                             []
% 2.25/0.98  --abstr_ref_prep                        false
% 2.25/0.98  --abstr_ref_until_sat                   false
% 2.25/0.98  --abstr_ref_sig_restrict                funpre
% 2.25/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.25/0.98  --abstr_ref_under                       []
% 2.25/0.98  
% 2.25/0.98  ------ SAT Options
% 2.25/0.98  
% 2.25/0.98  --sat_mode                              false
% 2.25/0.98  --sat_fm_restart_options                ""
% 2.25/0.98  --sat_gr_def                            false
% 2.25/0.98  --sat_epr_types                         true
% 2.25/0.98  --sat_non_cyclic_types                  false
% 2.25/0.98  --sat_finite_models                     false
% 2.25/0.98  --sat_fm_lemmas                         false
% 2.25/0.98  --sat_fm_prep                           false
% 2.25/0.98  --sat_fm_uc_incr                        true
% 2.25/0.98  --sat_out_model                         small
% 2.25/0.98  --sat_out_clauses                       false
% 2.25/0.98  
% 2.25/0.98  ------ QBF Options
% 2.25/0.98  
% 2.25/0.98  --qbf_mode                              false
% 2.25/0.98  --qbf_elim_univ                         false
% 2.25/0.98  --qbf_dom_inst                          none
% 2.25/0.98  --qbf_dom_pre_inst                      false
% 2.25/0.98  --qbf_sk_in                             false
% 2.25/0.98  --qbf_pred_elim                         true
% 2.25/0.98  --qbf_split                             512
% 2.25/0.98  
% 2.25/0.98  ------ BMC1 Options
% 2.25/0.98  
% 2.25/0.98  --bmc1_incremental                      false
% 2.25/0.98  --bmc1_axioms                           reachable_all
% 2.25/0.98  --bmc1_min_bound                        0
% 2.25/0.98  --bmc1_max_bound                        -1
% 2.25/0.98  --bmc1_max_bound_default                -1
% 2.25/0.98  --bmc1_symbol_reachability              true
% 2.25/0.98  --bmc1_property_lemmas                  false
% 2.25/0.98  --bmc1_k_induction                      false
% 2.25/0.98  --bmc1_non_equiv_states                 false
% 2.25/0.98  --bmc1_deadlock                         false
% 2.25/0.98  --bmc1_ucm                              false
% 2.25/0.98  --bmc1_add_unsat_core                   none
% 2.25/0.98  --bmc1_unsat_core_children              false
% 2.25/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.25/0.98  --bmc1_out_stat                         full
% 2.25/0.98  --bmc1_ground_init                      false
% 2.25/0.98  --bmc1_pre_inst_next_state              false
% 2.25/0.98  --bmc1_pre_inst_state                   false
% 2.25/0.98  --bmc1_pre_inst_reach_state             false
% 2.25/0.98  --bmc1_out_unsat_core                   false
% 2.25/0.98  --bmc1_aig_witness_out                  false
% 2.25/0.98  --bmc1_verbose                          false
% 2.25/0.98  --bmc1_dump_clauses_tptp                false
% 2.25/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.25/0.98  --bmc1_dump_file                        -
% 2.25/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.25/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.25/0.98  --bmc1_ucm_extend_mode                  1
% 2.25/0.98  --bmc1_ucm_init_mode                    2
% 2.25/0.98  --bmc1_ucm_cone_mode                    none
% 2.25/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.25/0.98  --bmc1_ucm_relax_model                  4
% 2.25/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.25/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.25/0.98  --bmc1_ucm_layered_model                none
% 2.25/0.98  --bmc1_ucm_max_lemma_size               10
% 2.25/0.98  
% 2.25/0.98  ------ AIG Options
% 2.25/0.98  
% 2.25/0.98  --aig_mode                              false
% 2.25/0.98  
% 2.25/0.98  ------ Instantiation Options
% 2.25/0.98  
% 2.25/0.98  --instantiation_flag                    true
% 2.25/0.98  --inst_sos_flag                         false
% 2.25/0.98  --inst_sos_phase                        true
% 2.25/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.25/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.25/0.98  --inst_lit_sel_side                     none
% 2.25/0.98  --inst_solver_per_active                1400
% 2.25/0.98  --inst_solver_calls_frac                1.
% 2.25/0.98  --inst_passive_queue_type               priority_queues
% 2.25/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.25/0.98  --inst_passive_queues_freq              [25;2]
% 2.25/0.98  --inst_dismatching                      true
% 2.25/0.98  --inst_eager_unprocessed_to_passive     true
% 2.25/0.98  --inst_prop_sim_given                   true
% 2.25/0.98  --inst_prop_sim_new                     false
% 2.25/0.98  --inst_subs_new                         false
% 2.25/0.98  --inst_eq_res_simp                      false
% 2.25/0.98  --inst_subs_given                       false
% 2.25/0.98  --inst_orphan_elimination               true
% 2.25/0.98  --inst_learning_loop_flag               true
% 2.25/0.98  --inst_learning_start                   3000
% 2.25/0.98  --inst_learning_factor                  2
% 2.25/0.98  --inst_start_prop_sim_after_learn       3
% 2.25/0.98  --inst_sel_renew                        solver
% 2.25/0.98  --inst_lit_activity_flag                true
% 2.25/0.98  --inst_restr_to_given                   false
% 2.25/0.98  --inst_activity_threshold               500
% 2.25/0.98  --inst_out_proof                        true
% 2.25/0.98  
% 2.25/0.98  ------ Resolution Options
% 2.25/0.98  
% 2.25/0.98  --resolution_flag                       false
% 2.25/0.98  --res_lit_sel                           adaptive
% 2.25/0.98  --res_lit_sel_side                      none
% 2.25/0.98  --res_ordering                          kbo
% 2.25/0.98  --res_to_prop_solver                    active
% 2.25/0.98  --res_prop_simpl_new                    false
% 2.25/0.98  --res_prop_simpl_given                  true
% 2.25/0.98  --res_passive_queue_type                priority_queues
% 2.25/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.25/0.98  --res_passive_queues_freq               [15;5]
% 2.25/0.98  --res_forward_subs                      full
% 2.25/0.98  --res_backward_subs                     full
% 2.25/0.98  --res_forward_subs_resolution           true
% 2.25/0.98  --res_backward_subs_resolution          true
% 2.25/0.98  --res_orphan_elimination                true
% 2.25/0.98  --res_time_limit                        2.
% 2.25/0.98  --res_out_proof                         true
% 2.25/0.98  
% 2.25/0.98  ------ Superposition Options
% 2.25/0.98  
% 2.25/0.98  --superposition_flag                    true
% 2.25/0.98  --sup_passive_queue_type                priority_queues
% 2.25/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.25/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.25/0.98  --demod_completeness_check              fast
% 2.25/0.98  --demod_use_ground                      true
% 2.25/0.98  --sup_to_prop_solver                    passive
% 2.25/0.98  --sup_prop_simpl_new                    true
% 2.25/0.98  --sup_prop_simpl_given                  true
% 2.25/0.98  --sup_fun_splitting                     false
% 2.25/0.98  --sup_smt_interval                      50000
% 2.25/0.98  
% 2.25/0.98  ------ Superposition Simplification Setup
% 2.25/0.98  
% 2.25/0.98  --sup_indices_passive                   []
% 2.25/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.25/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.98  --sup_full_bw                           [BwDemod]
% 2.25/0.98  --sup_immed_triv                        [TrivRules]
% 2.25/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.98  --sup_immed_bw_main                     []
% 2.25/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.25/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.98  
% 2.25/0.98  ------ Combination Options
% 2.25/0.98  
% 2.25/0.98  --comb_res_mult                         3
% 2.25/0.98  --comb_sup_mult                         2
% 2.25/0.98  --comb_inst_mult                        10
% 2.25/0.98  
% 2.25/0.98  ------ Debug Options
% 2.25/0.98  
% 2.25/0.98  --dbg_backtrace                         false
% 2.25/0.98  --dbg_dump_prop_clauses                 false
% 2.25/0.98  --dbg_dump_prop_clauses_file            -
% 2.25/0.98  --dbg_out_stat                          false
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  ------ Proving...
% 2.25/0.98  
% 2.25/0.98  
% 2.25/0.98  % SZS status Theorem for theBenchmark.p
% 2.25/0.98  
% 2.25/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.25/0.98  
% 2.25/0.98  fof(f3,axiom,(
% 2.25/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f46,plain,(
% 2.25/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f3])).
% 2.25/0.98  
% 2.25/0.98  fof(f12,axiom,(
% 2.25/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f30,plain,(
% 2.25/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.25/0.98    inference(ennf_transformation,[],[f12])).
% 2.25/0.98  
% 2.25/0.98  fof(f56,plain,(
% 2.25/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f30])).
% 2.25/0.98  
% 2.25/0.98  fof(f9,axiom,(
% 2.25/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f25,plain,(
% 2.25/0.98    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.25/0.98    inference(ennf_transformation,[],[f9])).
% 2.25/0.98  
% 2.25/0.98  fof(f41,plain,(
% 2.25/0.98    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.25/0.98    inference(nnf_transformation,[],[f25])).
% 2.25/0.98  
% 2.25/0.98  fof(f53,plain,(
% 2.25/0.98    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f41])).
% 2.25/0.98  
% 2.25/0.98  fof(f11,axiom,(
% 2.25/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f28,plain,(
% 2.25/0.98    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.25/0.98    inference(ennf_transformation,[],[f11])).
% 2.25/0.98  
% 2.25/0.98  fof(f29,plain,(
% 2.25/0.98    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.25/0.98    inference(flattening,[],[f28])).
% 2.25/0.98  
% 2.25/0.98  fof(f55,plain,(
% 2.25/0.98    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f29])).
% 2.25/0.98  
% 2.25/0.98  fof(f18,conjecture,(
% 2.25/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f19,negated_conjecture,(
% 2.25/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.25/0.98    inference(negated_conjecture,[],[f18])).
% 2.25/0.98  
% 2.25/0.98  fof(f37,plain,(
% 2.25/0.98    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.25/0.98    inference(ennf_transformation,[],[f19])).
% 2.25/0.98  
% 2.25/0.98  fof(f38,plain,(
% 2.25/0.98    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.25/0.98    inference(flattening,[],[f37])).
% 2.25/0.98  
% 2.25/0.98  fof(f42,plain,(
% 2.25/0.98    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 2.25/0.98    introduced(choice_axiom,[])).
% 2.25/0.98  
% 2.25/0.98  fof(f43,plain,(
% 2.25/0.98    ~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 2.25/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f38,f42])).
% 2.25/0.98  
% 2.25/0.98  fof(f62,plain,(
% 2.25/0.98    v1_funct_1(sK3)),
% 2.25/0.98    inference(cnf_transformation,[],[f43])).
% 2.25/0.98  
% 2.25/0.98  fof(f64,plain,(
% 2.25/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.25/0.98    inference(cnf_transformation,[],[f43])).
% 2.25/0.98  
% 2.25/0.98  fof(f4,axiom,(
% 2.25/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f47,plain,(
% 2.25/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.25/0.98    inference(cnf_transformation,[],[f4])).
% 2.25/0.98  
% 2.25/0.98  fof(f69,plain,(
% 2.25/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2)))),
% 2.25/0.98    inference(definition_unfolding,[],[f64,f47])).
% 2.25/0.98  
% 2.25/0.98  fof(f13,axiom,(
% 2.25/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f31,plain,(
% 2.25/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.98    inference(ennf_transformation,[],[f13])).
% 2.25/0.98  
% 2.25/0.98  fof(f57,plain,(
% 2.25/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.25/0.98    inference(cnf_transformation,[],[f31])).
% 2.25/0.98  
% 2.25/0.98  fof(f16,axiom,(
% 2.25/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.25/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.98  
% 2.25/0.98  fof(f34,plain,(
% 2.25/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.99    inference(ennf_transformation,[],[f16])).
% 2.25/0.99  
% 2.25/0.99  fof(f60,plain,(
% 2.25/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.25/0.99    inference(cnf_transformation,[],[f34])).
% 2.25/0.99  
% 2.25/0.99  fof(f15,axiom,(
% 2.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f33,plain,(
% 2.25/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.99    inference(ennf_transformation,[],[f15])).
% 2.25/0.99  
% 2.25/0.99  fof(f59,plain,(
% 2.25/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.25/0.99    inference(cnf_transformation,[],[f33])).
% 2.25/0.99  
% 2.25/0.99  fof(f6,axiom,(
% 2.25/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f22,plain,(
% 2.25/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f6])).
% 2.25/0.99  
% 2.25/0.99  fof(f49,plain,(
% 2.25/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.25/0.99    inference(cnf_transformation,[],[f22])).
% 2.25/0.99  
% 2.25/0.99  fof(f66,plain,(
% 2.25/0.99    ~r2_hidden(k1_funct_1(sK3,sK1),sK2)),
% 2.25/0.99    inference(cnf_transformation,[],[f43])).
% 2.25/0.99  
% 2.25/0.99  fof(f7,axiom,(
% 2.25/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f23,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.25/0.99    inference(ennf_transformation,[],[f7])).
% 2.25/0.99  
% 2.25/0.99  fof(f50,plain,(
% 2.25/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f23])).
% 2.25/0.99  
% 2.25/0.99  fof(f68,plain,(
% 2.25/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1)) | ~v1_relat_1(X0)) )),
% 2.25/0.99    inference(definition_unfolding,[],[f50,f47])).
% 2.25/0.99  
% 2.25/0.99  fof(f14,axiom,(
% 2.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f20,plain,(
% 2.25/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.25/0.99    inference(pure_predicate_removal,[],[f14])).
% 2.25/0.99  
% 2.25/0.99  fof(f32,plain,(
% 2.25/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.25/0.99    inference(ennf_transformation,[],[f20])).
% 2.25/0.99  
% 2.25/0.99  fof(f58,plain,(
% 2.25/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.25/0.99    inference(cnf_transformation,[],[f32])).
% 2.25/0.99  
% 2.25/0.99  fof(f10,axiom,(
% 2.25/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f26,plain,(
% 2.25/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.25/0.99    inference(ennf_transformation,[],[f10])).
% 2.25/0.99  
% 2.25/0.99  fof(f27,plain,(
% 2.25/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.25/0.99    inference(flattening,[],[f26])).
% 2.25/0.99  
% 2.25/0.99  fof(f54,plain,(
% 2.25/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f27])).
% 2.25/0.99  
% 2.25/0.99  fof(f8,axiom,(
% 2.25/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f24,plain,(
% 2.25/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.25/0.99    inference(ennf_transformation,[],[f8])).
% 2.25/0.99  
% 2.25/0.99  fof(f51,plain,(
% 2.25/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f24])).
% 2.25/0.99  
% 2.25/0.99  fof(f17,axiom,(
% 2.25/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 2.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f35,plain,(
% 2.25/0.99    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.25/0.99    inference(ennf_transformation,[],[f17])).
% 2.25/0.99  
% 2.25/0.99  fof(f36,plain,(
% 2.25/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.25/0.99    inference(flattening,[],[f35])).
% 2.25/0.99  
% 2.25/0.99  fof(f61,plain,(
% 2.25/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f36])).
% 2.25/0.99  
% 2.25/0.99  fof(f63,plain,(
% 2.25/0.99    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 2.25/0.99    inference(cnf_transformation,[],[f43])).
% 2.25/0.99  
% 2.25/0.99  fof(f70,plain,(
% 2.25/0.99    v1_funct_2(sK3,k2_tarski(sK1,sK1),sK2)),
% 2.25/0.99    inference(definition_unfolding,[],[f63,f47])).
% 2.25/0.99  
% 2.25/0.99  fof(f65,plain,(
% 2.25/0.99    k1_xboole_0 != sK2),
% 2.25/0.99    inference(cnf_transformation,[],[f43])).
% 2.25/0.99  
% 2.25/0.99  fof(f2,axiom,(
% 2.25/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f21,plain,(
% 2.25/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.25/0.99    inference(ennf_transformation,[],[f2])).
% 2.25/0.99  
% 2.25/0.99  fof(f39,plain,(
% 2.25/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.25/0.99    introduced(choice_axiom,[])).
% 2.25/0.99  
% 2.25/0.99  fof(f40,plain,(
% 2.25/0.99    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f39])).
% 2.25/0.99  
% 2.25/0.99  fof(f45,plain,(
% 2.25/0.99    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.25/0.99    inference(cnf_transformation,[],[f40])).
% 2.25/0.99  
% 2.25/0.99  fof(f1,axiom,(
% 2.25/0.99    v1_xboole_0(k1_xboole_0)),
% 2.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f44,plain,(
% 2.25/0.99    v1_xboole_0(k1_xboole_0)),
% 2.25/0.99    inference(cnf_transformation,[],[f1])).
% 2.25/0.99  
% 2.25/0.99  fof(f5,axiom,(
% 2.25/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.25/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f48,plain,(
% 2.25/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.25/0.99    inference(cnf_transformation,[],[f5])).
% 2.25/0.99  
% 2.25/0.99  fof(f67,plain,(
% 2.25/0.99    ( ! [X0] : (~v1_xboole_0(k2_tarski(X0,X0))) )),
% 2.25/0.99    inference(definition_unfolding,[],[f48,f47])).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2,plain,
% 2.25/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.25/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_11,plain,
% 2.25/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.25/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_249,plain,
% 2.25/0.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 2.25/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_250,plain,
% 2.25/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.25/0.99      inference(unflattening,[status(thm)],[c_249]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_585,plain,
% 2.25/0.99      ( ~ r2_hidden(X0_51,k1_xboole_0) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_250]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2186,plain,
% 2.25/0.99      ( ~ r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),k1_xboole_0) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_585]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_7,plain,
% 2.25/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 2.25/0.99      | ~ v1_relat_1(X1)
% 2.25/0.99      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 2.25/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_594,plain,
% 2.25/0.99      ( r2_hidden(X0_51,k1_relat_1(X0_52))
% 2.25/0.99      | ~ v1_relat_1(X0_52)
% 2.25/0.99      | k11_relat_1(X0_52,X0_51) = k1_xboole_0 ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_918,plain,
% 2.25/0.99      ( k11_relat_1(X0_52,X0_51) = k1_xboole_0
% 2.25/0.99      | r2_hidden(X0_51,k1_relat_1(X0_52)) = iProver_top
% 2.25/0.99      | v1_relat_1(X0_52) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_10,plain,
% 2.25/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.25/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.25/0.99      | ~ v1_funct_1(X1)
% 2.25/0.99      | ~ v1_relat_1(X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_21,negated_conjecture,
% 2.25/0.99      ( v1_funct_1(sK3) ),
% 2.25/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_301,plain,
% 2.25/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.25/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 2.25/0.99      | ~ v1_relat_1(X1)
% 2.25/0.99      | sK3 != X1 ),
% 2.25/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_302,plain,
% 2.25/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 2.25/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))
% 2.25/0.99      | ~ v1_relat_1(sK3) ),
% 2.25/0.99      inference(unflattening,[status(thm)],[c_301]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_582,plain,
% 2.25/0.99      ( ~ r2_hidden(X0_51,k1_relat_1(sK3))
% 2.25/0.99      | r2_hidden(k1_funct_1(sK3,X0_51),k2_relat_1(sK3))
% 2.25/0.99      | ~ v1_relat_1(sK3) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_302]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_928,plain,
% 2.25/0.99      ( r2_hidden(X0_51,k1_relat_1(sK3)) != iProver_top
% 2.25/0.99      | r2_hidden(k1_funct_1(sK3,X0_51),k2_relat_1(sK3)) = iProver_top
% 2.25/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_19,negated_conjecture,
% 2.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) ),
% 2.25/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_24,plain,
% 2.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_661,plain,
% 2.25/0.99      ( r2_hidden(X0_51,k1_relat_1(sK3)) != iProver_top
% 2.25/0.99      | r2_hidden(k1_funct_1(sK3,X0_51),k2_relat_1(sK3)) = iProver_top
% 2.25/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_12,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.25/0.99      | v1_relat_1(X0) ),
% 2.25/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_592,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 2.25/0.99      | v1_relat_1(X0_52) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1034,plain,
% 2.25/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2)))
% 2.25/0.99      | v1_relat_1(sK3) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_592]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1035,plain,
% 2.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) != iProver_top
% 2.25/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_1034]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1060,plain,
% 2.25/0.99      ( r2_hidden(k1_funct_1(sK3,X0_51),k2_relat_1(sK3)) = iProver_top
% 2.25/0.99      | r2_hidden(X0_51,k1_relat_1(sK3)) != iProver_top ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_928,c_24,c_661,c_1035]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1061,plain,
% 2.25/0.99      ( r2_hidden(X0_51,k1_relat_1(sK3)) != iProver_top
% 2.25/0.99      | r2_hidden(k1_funct_1(sK3,X0_51),k2_relat_1(sK3)) = iProver_top ),
% 2.25/0.99      inference(renaming,[status(thm)],[c_1060]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_587,negated_conjecture,
% 2.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_924,plain,
% 2.25/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_15,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.25/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.25/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_590,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 2.25/0.99      | k2_relset_1(X1_52,X2_52,X0_52) = k2_relat_1(X0_52) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_922,plain,
% 2.25/0.99      ( k2_relset_1(X0_52,X1_52,X2_52) = k2_relat_1(X2_52)
% 2.25/0.99      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1246,plain,
% 2.25/0.99      ( k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_924,c_922]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_14,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.25/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.25/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_591,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 2.25/0.99      | m1_subset_1(k2_relset_1(X1_52,X2_52,X0_52),k1_zfmisc_1(X2_52)) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_921,plain,
% 2.25/0.99      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
% 2.25/0.99      | m1_subset_1(k2_relset_1(X1_52,X2_52,X0_52),k1_zfmisc_1(X2_52)) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_591]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1511,plain,
% 2.25/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 2.25/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2))) != iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_1246,c_921]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1687,plain,
% 2.25/0.99      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_1511,c_24]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.25/0.99      | ~ r2_hidden(X2,X0)
% 2.25/0.99      | r2_hidden(X2,X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_597,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 2.25/0.99      | ~ r2_hidden(X0_51,X0_52)
% 2.25/0.99      | r2_hidden(X0_51,X1_52) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_915,plain,
% 2.25/0.99      ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top
% 2.25/0.99      | r2_hidden(X0_51,X0_52) != iProver_top
% 2.25/0.99      | r2_hidden(X0_51,X1_52) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1692,plain,
% 2.25/0.99      ( r2_hidden(X0_51,k2_relat_1(sK3)) != iProver_top
% 2.25/0.99      | r2_hidden(X0_51,sK2) = iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_1687,c_915]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1739,plain,
% 2.25/0.99      ( r2_hidden(X0_51,k1_relat_1(sK3)) != iProver_top
% 2.25/0.99      | r2_hidden(k1_funct_1(sK3,X0_51),sK2) = iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_1061,c_1692]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_17,negated_conjecture,
% 2.25/0.99      ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
% 2.25/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_589,negated_conjecture,
% 2.25/0.99      ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_923,plain,
% 2.25/0.99      ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_589]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1835,plain,
% 2.25/0.99      ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_1739,c_923]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1839,plain,
% 2.25/0.99      ( k11_relat_1(sK3,sK1) = k1_xboole_0
% 2.25/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_918,c_1835]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_920,plain,
% 2.25/0.99      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
% 2.25/0.99      | v1_relat_1(X0_52) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1165,plain,
% 2.25/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_924,c_920]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5,plain,
% 2.25/0.99      ( ~ v1_relat_1(X0)
% 2.25/0.99      | k9_relat_1(X0,k2_tarski(X1,X1)) = k11_relat_1(X0,X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_596,plain,
% 2.25/0.99      ( ~ v1_relat_1(X0_52)
% 2.25/0.99      | k9_relat_1(X0_52,k2_tarski(X0_51,X0_51)) = k11_relat_1(X0_52,X0_51) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_916,plain,
% 2.25/0.99      ( k9_relat_1(X0_52,k2_tarski(X0_51,X0_51)) = k11_relat_1(X0_52,X0_51)
% 2.25/0.99      | v1_relat_1(X0_52) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1272,plain,
% 2.25/0.99      ( k9_relat_1(sK3,k2_tarski(X0_51,X0_51)) = k11_relat_1(sK3,X0_51) ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_1165,c_916]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_13,plain,
% 2.25/0.99      ( v4_relat_1(X0,X1)
% 2.25/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.25/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_9,plain,
% 2.25/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.25/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_260,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.25/0.99      | ~ v1_relat_1(X0)
% 2.25/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.25/0.99      inference(resolution,[status(thm)],[c_13,c_9]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_264,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.25/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_260,c_13,c_12,c_9]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_584,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 2.25/0.99      | k7_relat_1(X0_52,X1_52) = X0_52 ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_264]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_926,plain,
% 2.25/0.99      ( k7_relat_1(X0_52,X1_52) = X0_52
% 2.25/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1431,plain,
% 2.25/0.99      ( k7_relat_1(sK3,k2_tarski(sK1,sK1)) = sK3 ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_924,c_926]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_6,plain,
% 2.25/0.99      ( ~ v1_relat_1(X0)
% 2.25/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_595,plain,
% 2.25/0.99      ( ~ v1_relat_1(X0_52)
% 2.25/0.99      | k2_relat_1(k7_relat_1(X0_52,X1_52)) = k9_relat_1(X0_52,X1_52) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_917,plain,
% 2.25/0.99      ( k2_relat_1(k7_relat_1(X0_52,X1_52)) = k9_relat_1(X0_52,X1_52)
% 2.25/0.99      | v1_relat_1(X0_52) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1273,plain,
% 2.25/0.99      ( k2_relat_1(k7_relat_1(sK3,X0_52)) = k9_relat_1(sK3,X0_52) ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_1165,c_917]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1433,plain,
% 2.25/0.99      ( k9_relat_1(sK3,k2_tarski(sK1,sK1)) = k2_relat_1(sK3) ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_1431,c_1273]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1697,plain,
% 2.25/0.99      ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_1272,c_1433]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1840,plain,
% 2.25/0.99      ( k2_relat_1(sK3) = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.25/0.99      inference(demodulation,[status(thm)],[c_1839,c_1697]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1932,plain,
% 2.25/0.99      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_1840,c_24,c_1035]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1940,plain,
% 2.25/0.99      ( k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3) = k1_xboole_0 ),
% 2.25/0.99      inference(demodulation,[status(thm)],[c_1932,c_1246]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_600,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1806,plain,
% 2.25/0.99      ( k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) = k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_600]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_604,plain,
% 2.25/0.99      ( ~ r2_hidden(X0_51,X0_52)
% 2.25/0.99      | r2_hidden(X1_51,X1_52)
% 2.25/0.99      | X1_52 != X0_52
% 2.25/0.99      | X1_51 != X0_51 ),
% 2.25/0.99      theory(equality) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1449,plain,
% 2.25/0.99      ( r2_hidden(X0_51,X0_52)
% 2.25/0.99      | ~ r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3))
% 2.25/0.99      | X0_52 != k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)
% 2.25/0.99      | X0_51 != k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_604]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1805,plain,
% 2.25/0.99      ( r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),X0_52)
% 2.25/0.99      | ~ r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3))
% 2.25/0.99      | X0_52 != k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)
% 2.25/0.99      | k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) != k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_1449]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1808,plain,
% 2.25/0.99      ( ~ r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3))
% 2.25/0.99      | r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),k1_xboole_0)
% 2.25/0.99      | k1_xboole_0 != k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)
% 2.25/0.99      | k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) != k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_1805]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_16,plain,
% 2.25/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.25/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.25/0.99      | ~ r2_hidden(X3,X1)
% 2.25/0.99      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.25/0.99      | ~ v1_funct_1(X0)
% 2.25/0.99      | k1_xboole_0 = X2 ),
% 2.25/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_20,negated_conjecture,
% 2.25/0.99      ( v1_funct_2(sK3,k2_tarski(sK1,sK1),sK2) ),
% 2.25/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_280,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.25/0.99      | ~ r2_hidden(X3,X1)
% 2.25/0.99      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 2.25/0.99      | ~ v1_funct_1(X0)
% 2.25/0.99      | k2_tarski(sK1,sK1) != X1
% 2.25/0.99      | sK2 != X2
% 2.25/0.99      | sK3 != X0
% 2.25/0.99      | k1_xboole_0 = X2 ),
% 2.25/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_281,plain,
% 2.25/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_tarski(sK1,sK1),sK2)))
% 2.25/0.99      | ~ r2_hidden(X0,k2_tarski(sK1,sK1))
% 2.25/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3))
% 2.25/0.99      | ~ v1_funct_1(sK3)
% 2.25/0.99      | k1_xboole_0 = sK2 ),
% 2.25/0.99      inference(unflattening,[status(thm)],[c_280]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_18,negated_conjecture,
% 2.25/0.99      ( k1_xboole_0 != sK2 ),
% 2.25/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_285,plain,
% 2.25/0.99      ( ~ r2_hidden(X0,k2_tarski(sK1,sK1))
% 2.25/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)) ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_281,c_21,c_19,c_18]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_583,plain,
% 2.25/0.99      ( ~ r2_hidden(X0_51,k2_tarski(sK1,sK1))
% 2.25/0.99      | r2_hidden(k1_funct_1(sK3,X0_51),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_285]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1400,plain,
% 2.25/0.99      ( r2_hidden(k1_funct_1(sK3,sK0(k2_tarski(sK1,sK1))),k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3))
% 2.25/0.99      | ~ r2_hidden(sK0(k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_583]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_603,plain,
% 2.25/0.99      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 2.25/0.99      theory(equality) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1373,plain,
% 2.25/0.99      ( X0_52 != X1_52
% 2.25/0.99      | X0_52 = k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)
% 2.25/0.99      | k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3) != X1_52 ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_603]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1374,plain,
% 2.25/0.99      ( k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3) != k1_xboole_0
% 2.25/0.99      | k1_xboole_0 = k2_relset_1(k2_tarski(sK1,sK1),sK2,sK3)
% 2.25/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_1373]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1,plain,
% 2.25/0.99      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.25/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_598,plain,
% 2.25/0.99      ( r2_hidden(sK0(X0_52),X0_52) | k1_xboole_0 = X0_52 ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1286,plain,
% 2.25/0.99      ( r2_hidden(sK0(k2_tarski(X0_51,X0_51)),k2_tarski(X0_51,X0_51))
% 2.25/0.99      | k1_xboole_0 = k2_tarski(X0_51,X0_51) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_598]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1288,plain,
% 2.25/0.99      ( r2_hidden(sK0(k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
% 2.25/0.99      | k1_xboole_0 = k2_tarski(sK1,sK1) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_1286]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1045,plain,
% 2.25/0.99      ( k2_tarski(X0_51,X0_51) != X0_52
% 2.25/0.99      | k2_tarski(X0_51,X0_51) = k1_xboole_0
% 2.25/0.99      | k1_xboole_0 != X0_52 ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_603]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1133,plain,
% 2.25/0.99      ( k2_tarski(X0_51,X0_51) != k2_tarski(X0_51,X0_51)
% 2.25/0.99      | k2_tarski(X0_51,X0_51) = k1_xboole_0
% 2.25/0.99      | k1_xboole_0 != k2_tarski(X0_51,X0_51) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_1045]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1135,plain,
% 2.25/0.99      ( k2_tarski(sK1,sK1) != k2_tarski(sK1,sK1)
% 2.25/0.99      | k2_tarski(sK1,sK1) = k1_xboole_0
% 2.25/0.99      | k1_xboole_0 != k2_tarski(sK1,sK1) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_1133]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_0,plain,
% 2.25/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.25/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3,plain,
% 2.25/0.99      ( ~ v1_xboole_0(k2_tarski(X0,X0)) ),
% 2.25/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_243,plain,
% 2.25/0.99      ( k2_tarski(X0,X0) != k1_xboole_0 ),
% 2.25/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_3]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_586,plain,
% 2.25/0.99      ( k2_tarski(X0_51,X0_51) != k1_xboole_0 ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_243]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_651,plain,
% 2.25/0.99      ( k2_tarski(sK1,sK1) != k1_xboole_0 ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_586]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_601,plain,( X0_52 = X0_52 ),theory(equality) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_628,plain,
% 2.25/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_601]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_627,plain,
% 2.25/0.99      ( sK1 = sK1 ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_600]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_605,plain,
% 2.25/0.99      ( k2_tarski(X0_51,X1_51) = k2_tarski(X2_51,X3_51)
% 2.25/0.99      | X0_51 != X2_51
% 2.25/0.99      | X1_51 != X3_51 ),
% 2.25/0.99      theory(equality) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_616,plain,
% 2.25/0.99      ( k2_tarski(sK1,sK1) = k2_tarski(sK1,sK1) | sK1 != sK1 ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_605]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(contradiction,plain,
% 2.25/0.99      ( $false ),
% 2.25/0.99      inference(minisat,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_2186,c_1940,c_1806,c_1808,c_1400,c_1374,c_1288,c_1135,
% 2.25/0.99                 c_651,c_628,c_627,c_616]) ).
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.25/0.99  
% 2.25/0.99  ------                               Statistics
% 2.25/0.99  
% 2.25/0.99  ------ General
% 2.25/0.99  
% 2.25/0.99  abstr_ref_over_cycles:                  0
% 2.25/0.99  abstr_ref_under_cycles:                 0
% 2.25/0.99  gc_basic_clause_elim:                   0
% 2.25/0.99  forced_gc_time:                         0
% 2.25/0.99  parsing_time:                           0.009
% 2.25/0.99  unif_index_cands_time:                  0.
% 2.25/0.99  unif_index_add_time:                    0.
% 2.25/0.99  orderings_time:                         0.
% 2.25/0.99  out_proof_time:                         0.013
% 2.25/0.99  total_time:                             0.107
% 2.25/0.99  num_of_symbols:                         57
% 2.25/0.99  num_of_terms:                           1999
% 2.25/0.99  
% 2.25/0.99  ------ Preprocessing
% 2.25/0.99  
% 2.25/0.99  num_of_splits:                          0
% 2.25/0.99  num_of_split_atoms:                     0
% 2.25/0.99  num_of_reused_defs:                     0
% 2.25/0.99  num_eq_ax_congr_red:                    26
% 2.25/0.99  num_of_sem_filtered_clauses:            1
% 2.25/0.99  num_of_subtypes:                        3
% 2.25/0.99  monotx_restored_types:                  1
% 2.25/0.99  sat_num_of_epr_types:                   0
% 2.25/0.99  sat_num_of_non_cyclic_types:            0
% 2.25/0.99  sat_guarded_non_collapsed_types:        1
% 2.25/0.99  num_pure_diseq_elim:                    0
% 2.25/0.99  simp_replaced_by:                       0
% 2.25/0.99  res_preprocessed:                       104
% 2.25/0.99  prep_upred:                             0
% 2.25/0.99  prep_unflattend:                        12
% 2.25/0.99  smt_new_axioms:                         0
% 2.25/0.99  pred_elim_cands:                        3
% 2.25/0.99  pred_elim:                              5
% 2.25/0.99  pred_elim_cl:                           5
% 2.25/0.99  pred_elim_cycles:                       7
% 2.25/0.99  merged_defs:                            0
% 2.25/0.99  merged_defs_ncl:                        0
% 2.25/0.99  bin_hyper_res:                          0
% 2.25/0.99  prep_cycles:                            4
% 2.25/0.99  pred_elim_time:                         0.004
% 2.25/0.99  splitting_time:                         0.
% 2.25/0.99  sem_filter_time:                        0.
% 2.25/0.99  monotx_time:                            0.
% 2.25/0.99  subtype_inf_time:                       0.001
% 2.25/0.99  
% 2.25/0.99  ------ Problem properties
% 2.25/0.99  
% 2.25/0.99  clauses:                                17
% 2.25/0.99  conjectures:                            3
% 2.25/0.99  epr:                                    2
% 2.25/0.99  horn:                                   15
% 2.25/0.99  ground:                                 3
% 2.25/0.99  unary:                                  5
% 2.25/0.99  binary:                                 8
% 2.25/0.99  lits:                                   33
% 2.25/0.99  lits_eq:                                9
% 2.25/0.99  fd_pure:                                0
% 2.25/0.99  fd_pseudo:                              0
% 2.25/0.99  fd_cond:                                1
% 2.25/0.99  fd_pseudo_cond:                         0
% 2.25/0.99  ac_symbols:                             0
% 2.25/0.99  
% 2.25/0.99  ------ Propositional Solver
% 2.25/0.99  
% 2.25/0.99  prop_solver_calls:                      28
% 2.25/0.99  prop_fast_solver_calls:                 554
% 2.25/0.99  smt_solver_calls:                       0
% 2.25/0.99  smt_fast_solver_calls:                  0
% 2.25/0.99  prop_num_of_clauses:                    754
% 2.25/0.99  prop_preprocess_simplified:             3452
% 2.25/0.99  prop_fo_subsumed:                       8
% 2.25/0.99  prop_solver_time:                       0.
% 2.25/0.99  smt_solver_time:                        0.
% 2.25/0.99  smt_fast_solver_time:                   0.
% 2.25/0.99  prop_fast_solver_time:                  0.
% 2.25/0.99  prop_unsat_core_time:                   0.
% 2.25/0.99  
% 2.25/0.99  ------ QBF
% 2.25/0.99  
% 2.25/0.99  qbf_q_res:                              0
% 2.25/0.99  qbf_num_tautologies:                    0
% 2.25/0.99  qbf_prep_cycles:                        0
% 2.25/0.99  
% 2.25/0.99  ------ BMC1
% 2.25/0.99  
% 2.25/0.99  bmc1_current_bound:                     -1
% 2.25/0.99  bmc1_last_solved_bound:                 -1
% 2.25/0.99  bmc1_unsat_core_size:                   -1
% 2.25/0.99  bmc1_unsat_core_parents_size:           -1
% 2.25/0.99  bmc1_merge_next_fun:                    0
% 2.25/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.25/0.99  
% 2.25/0.99  ------ Instantiation
% 2.25/0.99  
% 2.25/0.99  inst_num_of_clauses:                    234
% 2.25/0.99  inst_num_in_passive:                    70
% 2.25/0.99  inst_num_in_active:                     153
% 2.25/0.99  inst_num_in_unprocessed:                10
% 2.25/0.99  inst_num_of_loops:                      184
% 2.25/0.99  inst_num_of_learning_restarts:          0
% 2.25/0.99  inst_num_moves_active_passive:          25
% 2.25/0.99  inst_lit_activity:                      0
% 2.25/0.99  inst_lit_activity_moves:                0
% 2.25/0.99  inst_num_tautologies:                   0
% 2.25/0.99  inst_num_prop_implied:                  0
% 2.25/0.99  inst_num_existing_simplified:           0
% 2.25/0.99  inst_num_eq_res_simplified:             0
% 2.25/0.99  inst_num_child_elim:                    0
% 2.25/0.99  inst_num_of_dismatching_blockings:      30
% 2.25/0.99  inst_num_of_non_proper_insts:           165
% 2.25/0.99  inst_num_of_duplicates:                 0
% 2.25/0.99  inst_inst_num_from_inst_to_res:         0
% 2.25/0.99  inst_dismatching_checking_time:         0.
% 2.25/0.99  
% 2.25/0.99  ------ Resolution
% 2.25/0.99  
% 2.25/0.99  res_num_of_clauses:                     0
% 2.25/0.99  res_num_in_passive:                     0
% 2.25/0.99  res_num_in_active:                      0
% 2.25/0.99  res_num_of_loops:                       108
% 2.25/0.99  res_forward_subset_subsumed:            23
% 2.25/0.99  res_backward_subset_subsumed:           0
% 2.25/0.99  res_forward_subsumed:                   0
% 2.25/0.99  res_backward_subsumed:                  0
% 2.25/0.99  res_forward_subsumption_resolution:     0
% 2.25/0.99  res_backward_subsumption_resolution:    0
% 2.25/0.99  res_clause_to_clause_subsumption:       59
% 2.25/0.99  res_orphan_elimination:                 0
% 2.25/0.99  res_tautology_del:                      27
% 2.25/0.99  res_num_eq_res_simplified:              0
% 2.25/0.99  res_num_sel_changes:                    0
% 2.25/0.99  res_moves_from_active_to_pass:          0
% 2.25/0.99  
% 2.25/0.99  ------ Superposition
% 2.25/0.99  
% 2.25/0.99  sup_time_total:                         0.
% 2.25/0.99  sup_time_generating:                    0.
% 2.25/0.99  sup_time_sim_full:                      0.
% 2.25/0.99  sup_time_sim_immed:                     0.
% 2.25/0.99  
% 2.25/0.99  sup_num_of_clauses:                     36
% 2.25/0.99  sup_num_in_active:                      24
% 2.25/0.99  sup_num_in_passive:                     12
% 2.25/0.99  sup_num_of_loops:                       36
% 2.25/0.99  sup_fw_superposition:                   13
% 2.25/0.99  sup_bw_superposition:                   15
% 2.25/0.99  sup_immediate_simplified:               5
% 2.25/0.99  sup_given_eliminated:                   1
% 2.25/0.99  comparisons_done:                       0
% 2.25/0.99  comparisons_avoided:                    0
% 2.25/0.99  
% 2.25/0.99  ------ Simplifications
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  sim_fw_subset_subsumed:                 2
% 2.25/0.99  sim_bw_subset_subsumed:                 3
% 2.25/0.99  sim_fw_subsumed:                        2
% 2.25/0.99  sim_bw_subsumed:                        0
% 2.25/0.99  sim_fw_subsumption_res:                 1
% 2.25/0.99  sim_bw_subsumption_res:                 0
% 2.25/0.99  sim_tautology_del:                      0
% 2.25/0.99  sim_eq_tautology_del:                   1
% 2.25/0.99  sim_eq_res_simp:                        0
% 2.25/0.99  sim_fw_demodulated:                     1
% 2.25/0.99  sim_bw_demodulated:                     11
% 2.25/0.99  sim_light_normalised:                   1
% 2.25/0.99  sim_joinable_taut:                      0
% 2.25/0.99  sim_joinable_simp:                      0
% 2.25/0.99  sim_ac_normalised:                      0
% 2.25/0.99  sim_smt_subsumption:                    0
% 2.25/0.99  
%------------------------------------------------------------------------------
