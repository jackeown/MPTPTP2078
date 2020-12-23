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
% DateTime   : Thu Dec  3 12:05:59 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 690 expanded)
%              Number of clauses        :   63 ( 160 expanded)
%              Number of leaves         :   17 ( 170 expanded)
%              Depth                    :   21
%              Number of atoms          :  307 (1896 expanded)
%              Number of equality atoms :  170 ( 806 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
     => k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f60])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f40,f61])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK3,k1_tarski(sK0),sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f33])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f57,f61])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f59,f61,f61])).

fof(f56,plain,(
    v1_funct_2(sK3,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f56,f61])).

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

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f38,f61,f61,f61])).

fof(f70,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f63])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f42,f61])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_6,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_760,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_263,plain,
    ( ~ v1_relat_1(sK3)
    | X0 != X1
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)) = X2
    | k1_relat_1(sK3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_245])).

cnf(c_264,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_757,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_264])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_282,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_19])).

cnf(c_283,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_589,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1142,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_283,c_589])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1240,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1142,c_5])).

cnf(c_1352,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1240,c_264])).

cnf(c_1453,plain,
    ( k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_757,c_1352])).

cnf(c_1454,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1453])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_333,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_334,plain,
    ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_905,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(equality_resolution,[status(thm)],[c_334])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_758,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_964,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_905,c_758])).

cnf(c_1461,plain,
    ( k4_xboole_0(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = k1_relat_1(sK3)
    | r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_964])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_297,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_298,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_460,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != sK3
    | sK1 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_298])).

cnf(c_461,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_462,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_18])).

cnf(c_463,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(renaming,[status(thm)],[c_462])).

cnf(c_519,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_463])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_342,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_343,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_861,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_343])).

cnf(c_1011,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_519,c_861])).

cnf(c_1464,plain,
    ( k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) = k1_relat_1(sK3)
    | r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1461,c_1011])).

cnf(c_1,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1040,plain,
    ( k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_1011,c_1])).

cnf(c_1042,plain,
    ( k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) != k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_1040,c_1011])).

cnf(c_2171,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1464,c_1042])).

cnf(c_756,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_1241,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1240])).

cnf(c_1291,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_756,c_1241])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_762,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1526,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1291,c_762])).

cnf(c_1825,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k11_relat_1(sK3,sK0) ),
    inference(superposition,[status(thm)],[c_1011,c_1526])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_759,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1296,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1291,c_759])).

cnf(c_1837,plain,
    ( k11_relat_1(sK3,sK0) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_1825,c_1296])).

cnf(c_2175,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2171,c_1837])).

cnf(c_2178,plain,
    ( v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_2175])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2178,c_1241])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:53:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.20/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/0.99  
% 3.20/0.99  ------  iProver source info
% 3.20/0.99  
% 3.20/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.20/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/0.99  git: non_committed_changes: false
% 3.20/0.99  git: last_make_outside_of_git: false
% 3.20/0.99  
% 3.20/0.99  ------ 
% 3.20/0.99  ------ Parsing...
% 3.20/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/0.99  ------ Proving...
% 3.20/0.99  ------ Problem Properties 
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  clauses                                 15
% 3.20/0.99  conjectures                             2
% 3.20/0.99  EPR                                     1
% 3.20/0.99  Horn                                    12
% 3.20/0.99  unary                                   5
% 3.20/0.99  binary                                  6
% 3.20/0.99  lits                                    30
% 3.20/0.99  lits eq                                 21
% 3.20/0.99  fd_pure                                 0
% 3.20/0.99  fd_pseudo                               0
% 3.20/0.99  fd_cond                                 0
% 3.20/0.99  fd_pseudo_cond                          1
% 3.20/0.99  AC symbols                              0
% 3.20/0.99  
% 3.20/0.99  ------ Input Options Time Limit: Unbounded
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  ------ 
% 3.20/0.99  Current options:
% 3.20/0.99  ------ 
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  ------ Proving...
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS status Theorem for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  fof(f9,axiom,(
% 3.20/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f21,plain,(
% 3.20/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.20/0.99    inference(ennf_transformation,[],[f9])).
% 3.20/0.99  
% 3.20/0.99  fof(f44,plain,(
% 3.20/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f21])).
% 3.20/0.99  
% 3.20/0.99  fof(f5,axiom,(
% 3.20/0.99    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f17,plain,(
% 3.20/0.99    ! [X0,X1] : (~r2_hidden(X1,X0) => k4_xboole_0(X0,k1_tarski(X1)) = X0)),
% 3.20/0.99    inference(unused_predicate_definition_removal,[],[f5])).
% 3.20/0.99  
% 3.20/0.99  fof(f18,plain,(
% 3.20/0.99    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0))),
% 3.20/0.99    inference(ennf_transformation,[],[f17])).
% 3.20/0.99  
% 3.20/0.99  fof(f40,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f18])).
% 3.20/0.99  
% 3.20/0.99  fof(f1,axiom,(
% 3.20/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f35,plain,(
% 3.20/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f1])).
% 3.20/0.99  
% 3.20/0.99  fof(f2,axiom,(
% 3.20/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f36,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f2])).
% 3.20/0.99  
% 3.20/0.99  fof(f3,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f37,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f3])).
% 3.20/0.99  
% 3.20/0.99  fof(f60,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f36,f37])).
% 3.20/0.99  
% 3.20/0.99  fof(f61,plain,(
% 3.20/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f35,f60])).
% 3.20/0.99  
% 3.20/0.99  fof(f64,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f40,f61])).
% 3.20/0.99  
% 3.20/0.99  fof(f11,axiom,(
% 3.20/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f23,plain,(
% 3.20/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.20/0.99    inference(ennf_transformation,[],[f11])).
% 3.20/0.99  
% 3.20/0.99  fof(f24,plain,(
% 3.20/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.20/0.99    inference(flattening,[],[f23])).
% 3.20/0.99  
% 3.20/0.99  fof(f46,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f24])).
% 3.20/0.99  
% 3.20/0.99  fof(f66,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f46,f61])).
% 3.20/0.99  
% 3.20/0.99  fof(f15,conjecture,(
% 3.20/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f16,negated_conjecture,(
% 3.20/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.20/0.99    inference(negated_conjecture,[],[f15])).
% 3.20/0.99  
% 3.20/0.99  fof(f29,plain,(
% 3.20/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 3.20/0.99    inference(ennf_transformation,[],[f16])).
% 3.20/0.99  
% 3.20/0.99  fof(f30,plain,(
% 3.20/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 3.20/0.99    inference(flattening,[],[f29])).
% 3.20/0.99  
% 3.20/0.99  fof(f33,plain,(
% 3.20/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f34,plain,(
% 3.20/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 3.20/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f33])).
% 3.20/0.99  
% 3.20/0.99  fof(f55,plain,(
% 3.20/0.99    v1_funct_1(sK3)),
% 3.20/0.99    inference(cnf_transformation,[],[f34])).
% 3.20/0.99  
% 3.20/0.99  fof(f6,axiom,(
% 3.20/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f19,plain,(
% 3.20/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.20/0.99    inference(ennf_transformation,[],[f6])).
% 3.20/0.99  
% 3.20/0.99  fof(f41,plain,(
% 3.20/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f19])).
% 3.20/0.99  
% 3.20/0.99  fof(f57,plain,(
% 3.20/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.20/0.99    inference(cnf_transformation,[],[f34])).
% 3.20/0.99  
% 3.20/0.99  fof(f68,plain,(
% 3.20/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 3.20/0.99    inference(definition_unfolding,[],[f57,f61])).
% 3.20/0.99  
% 3.20/0.99  fof(f8,axiom,(
% 3.20/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f43,plain,(
% 3.20/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f8])).
% 3.20/0.99  
% 3.20/0.99  fof(f13,axiom,(
% 3.20/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f26,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(ennf_transformation,[],[f13])).
% 3.20/0.99  
% 3.20/0.99  fof(f48,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f26])).
% 3.20/0.99  
% 3.20/0.99  fof(f59,plain,(
% 3.20/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 3.20/0.99    inference(cnf_transformation,[],[f34])).
% 3.20/0.99  
% 3.20/0.99  fof(f67,plain,(
% 3.20/0.99    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 3.20/0.99    inference(definition_unfolding,[],[f59,f61,f61])).
% 3.20/0.99  
% 3.20/0.99  fof(f56,plain,(
% 3.20/0.99    v1_funct_2(sK3,k1_tarski(sK0),sK1)),
% 3.20/0.99    inference(cnf_transformation,[],[f34])).
% 3.20/0.99  
% 3.20/0.99  fof(f69,plain,(
% 3.20/0.99    v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 3.20/0.99    inference(definition_unfolding,[],[f56,f61])).
% 3.20/0.99  
% 3.20/0.99  fof(f14,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f27,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(ennf_transformation,[],[f14])).
% 3.20/0.99  
% 3.20/0.99  fof(f28,plain,(
% 3.20/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(flattening,[],[f27])).
% 3.20/0.99  
% 3.20/0.99  fof(f32,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(nnf_transformation,[],[f28])).
% 3.20/0.99  
% 3.20/0.99  fof(f49,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f32])).
% 3.20/0.99  
% 3.20/0.99  fof(f58,plain,(
% 3.20/0.99    k1_xboole_0 != sK1),
% 3.20/0.99    inference(cnf_transformation,[],[f34])).
% 3.20/0.99  
% 3.20/0.99  fof(f12,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f25,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(ennf_transformation,[],[f12])).
% 3.20/0.99  
% 3.20/0.99  fof(f47,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f25])).
% 3.20/0.99  
% 3.20/0.99  fof(f4,axiom,(
% 3.20/0.99    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f31,plain,(
% 3.20/0.99    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 3.20/0.99    inference(nnf_transformation,[],[f4])).
% 3.20/0.99  
% 3.20/0.99  fof(f38,plain,(
% 3.20/0.99    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f31])).
% 3.20/0.99  
% 3.20/0.99  fof(f63,plain,(
% 3.20/0.99    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 3.20/0.99    inference(definition_unfolding,[],[f38,f61,f61,f61])).
% 3.20/0.99  
% 3.20/0.99  fof(f70,plain,(
% 3.20/0.99    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 3.20/0.99    inference(equality_resolution,[],[f63])).
% 3.20/0.99  
% 3.20/0.99  fof(f7,axiom,(
% 3.20/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f20,plain,(
% 3.20/0.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.20/0.99    inference(ennf_transformation,[],[f7])).
% 3.20/0.99  
% 3.20/0.99  fof(f42,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f20])).
% 3.20/0.99  
% 3.20/0.99  fof(f65,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f42,f61])).
% 3.20/0.99  
% 3.20/0.99  fof(f10,axiom,(
% 3.20/0.99    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.20/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f22,plain,(
% 3.20/0.99    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.20/0.99    inference(ennf_transformation,[],[f10])).
% 3.20/0.99  
% 3.20/0.99  fof(f45,plain,(
% 3.20/0.99    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f22])).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6,plain,
% 3.20/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_760,plain,
% 3.20/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 3.20/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2,plain,
% 3.20/0.99      ( r2_hidden(X0,X1)
% 3.20/0.99      | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 3.20/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8,plain,
% 3.20/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.20/0.99      | ~ v1_funct_1(X1)
% 3.20/0.99      | ~ v1_relat_1(X1)
% 3.20/0.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_21,negated_conjecture,
% 3.20/0.99      ( v1_funct_1(sK3) ),
% 3.20/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_244,plain,
% 3.20/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.20/0.99      | ~ v1_relat_1(X1)
% 3.20/0.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 3.20/0.99      | sK3 != X1 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_245,plain,
% 3.20/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.20/0.99      | ~ v1_relat_1(sK3)
% 3.20/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_244]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_263,plain,
% 3.20/0.99      ( ~ v1_relat_1(sK3)
% 3.20/0.99      | X0 != X1
% 3.20/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.20/0.99      | k4_xboole_0(X2,k2_enumset1(X1,X1,X1,X1)) = X2
% 3.20/0.99      | k1_relat_1(sK3) != X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_245]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_264,plain,
% 3.20/0.99      ( ~ v1_relat_1(sK3)
% 3.20/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.20/0.99      | k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_263]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_757,plain,
% 3.20/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.20/0.99      | k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3)
% 3.20/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_264]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.20/0.99      | ~ v1_relat_1(X1)
% 3.20/0.99      | v1_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_19,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_282,plain,
% 3.20/0.99      ( ~ v1_relat_1(X0)
% 3.20/0.99      | v1_relat_1(X1)
% 3.20/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
% 3.20/0.99      | sK3 != X1 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_19]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_283,plain,
% 3.20/0.99      ( ~ v1_relat_1(X0)
% 3.20/0.99      | v1_relat_1(sK3)
% 3.20/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_282]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_589,plain,( X0 = X0 ),theory(equality) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1142,plain,
% 3.20/0.99      ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 3.20/0.99      | v1_relat_1(sK3) ),
% 3.20/0.99      inference(resolution,[status(thm)],[c_283,c_589]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5,plain,
% 3.20/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1240,plain,
% 3.20/0.99      ( v1_relat_1(sK3) ),
% 3.20/0.99      inference(forward_subsumption_resolution,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_1142,c_5]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1352,plain,
% 3.20/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.20/0.99      | k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3) ),
% 3.20/0.99      inference(backward_subsumption_resolution,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_1240,c_264]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1453,plain,
% 3.20/0.99      ( k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3)
% 3.20/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_757,c_1352]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1454,plain,
% 3.20/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.20/0.99      | k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3) ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_1453]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_10,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.20/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_333,plain,
% 3.20/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.20/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.20/0.99      | sK3 != X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_334,plain,
% 3.20/0.99      ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
% 3.20/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_333]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_905,plain,
% 3.20/0.99      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_334]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_17,negated_conjecture,
% 3.20/0.99      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_758,plain,
% 3.20/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_964,plain,
% 3.20/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_905,c_758]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1461,plain,
% 3.20/0.99      ( k4_xboole_0(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = k1_relat_1(sK3)
% 3.20/0.99      | r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1454,c_964]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_20,negated_conjecture,
% 3.20/0.99      ( v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_16,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.20/0.99      | k1_xboole_0 = X2 ),
% 3.20/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_297,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.20/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.20/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.20/0.99      | sK3 != X0
% 3.20/0.99      | k1_xboole_0 = X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_298,plain,
% 3.20/0.99      ( ~ v1_funct_2(sK3,X0,X1)
% 3.20/0.99      | k1_relset_1(X0,X1,sK3) = X0
% 3.20/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.20/0.99      | k1_xboole_0 = X1 ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_297]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_460,plain,
% 3.20/0.99      ( k2_enumset1(sK0,sK0,sK0,sK0) != X0
% 3.20/0.99      | k1_relset_1(X0,X1,sK3) = X0
% 3.20/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.20/0.99      | sK3 != sK3
% 3.20/0.99      | sK1 != X1
% 3.20/0.99      | k1_xboole_0 = X1 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_298]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_461,plain,
% 3.20/0.99      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0)
% 3.20/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 3.20/0.99      | k1_xboole_0 = sK1 ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_460]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_18,negated_conjecture,
% 3.20/0.99      ( k1_xboole_0 != sK1 ),
% 3.20/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_462,plain,
% 3.20/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 3.20/0.99      | k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_461,c_18]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_463,plain,
% 3.20/0.99      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0)
% 3.20/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_462]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_519,plain,
% 3.20/0.99      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 3.20/0.99      inference(equality_resolution_simp,[status(thm)],[c_463]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_9,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_342,plain,
% 3.20/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.20/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.20/0.99      | sK3 != X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_343,plain,
% 3.20/0.99      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 3.20/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_342]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_861,plain,
% 3.20/0.99      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
% 3.20/0.99      inference(equality_resolution,[status(thm)],[c_343]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1011,plain,
% 3.20/0.99      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_519,c_861]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1464,plain,
% 3.20/0.99      ( k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) = k1_relat_1(sK3)
% 3.20/0.99      | r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_1461,c_1011]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1,plain,
% 3.20/0.99      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1040,plain,
% 3.20/0.99      ( k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1011,c_1]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1042,plain,
% 3.20/0.99      ( k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) != k1_relat_1(sK3) ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_1040,c_1011]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2171,plain,
% 3.20/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) != iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_1464,c_1042]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_756,plain,
% 3.20/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
% 3.20/0.99      | v1_relat_1(X0) != iProver_top
% 3.20/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1241,plain,
% 3.20/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_1240]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1291,plain,
% 3.20/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_756,c_1241]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4,plain,
% 3.20/0.99      ( ~ v1_relat_1(X0)
% 3.20/0.99      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_762,plain,
% 3.20/0.99      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.20/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1526,plain,
% 3.20/0.99      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1291,c_762]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1825,plain,
% 3.20/0.99      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k11_relat_1(sK3,sK0) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1011,c_1526]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7,plain,
% 3.20/0.99      ( ~ v1_relat_1(X0)
% 3.20/0.99      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_759,plain,
% 3.20/0.99      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.20/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1296,plain,
% 3.20/0.99      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1291,c_759]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1837,plain,
% 3.20/0.99      ( k11_relat_1(sK3,sK0) = k2_relat_1(sK3) ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_1825,c_1296]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2175,plain,
% 3.20/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 3.20/0.99      inference(light_normalisation,[status(thm)],[c_2171,c_1837]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2178,plain,
% 3.20/0.99      ( v1_relat_1(sK3) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_760,c_2175]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(contradiction,plain,
% 3.20/0.99      ( $false ),
% 3.20/0.99      inference(minisat,[status(thm)],[c_2178,c_1241]) ).
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  ------                               Statistics
% 3.20/0.99  
% 3.20/0.99  ------ Selected
% 3.20/0.99  
% 3.20/0.99  total_time:                             0.13
% 3.20/0.99  
%------------------------------------------------------------------------------
