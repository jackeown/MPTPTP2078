%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:55 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  146 (2067 expanded)
%              Number of clauses        :   73 ( 369 expanded)
%              Number of leaves         :   19 ( 562 expanded)
%              Depth                    :   20
%              Number of atoms          :  334 (4776 expanded)
%              Number of equality atoms :  188 (2485 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f39,plain,
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

fof(f40,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK3,k1_tarski(sK0),sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f39])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
     => k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f53,f69])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    v1_funct_2(sK3,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f66,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f44,f69,f69,f69])).

fof(f78,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f45,f69,f69,f69])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f67,f69,f69])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f69])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_603,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_623,plain,
    ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_616,plain,
    ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k11_relat_1(X0,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3741,plain,
    ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k11_relat_1(X0,X1)
    | k4_xboole_0(k1_relat_1(X0),k2_enumset1(X1,X1,X1,X1)) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_616])).

cnf(c_4108,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_603,c_3741])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_846,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3) ),
    inference(resolution,[status(thm)],[c_3,c_21])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_873,plain,
    ( v1_relat_1(sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_846,c_5])).

cnf(c_874,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_873])).

cnf(c_4405,plain,
    ( k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4108,c_874])).

cnf(c_4406,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_4405])).

cnf(c_605,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_614,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1328,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_605,c_614])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_607,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1014,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_607])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_25,plain,
    ( v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_77,plain,
    ( k4_xboole_0(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( X0 = X1
    | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_78,plain,
    ( k4_xboole_0(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_211,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_828,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_829,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_828])).

cnf(c_1261,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1014,c_25,c_20,c_77,c_78,c_829])).

cnf(c_1376,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1328,c_1261])).

cnf(c_1381,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1376,c_605])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_613,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2483,plain,
    ( k7_relset_1(k1_relat_1(sK3),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1381,c_613])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_606,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1380,plain,
    ( r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1376,c_606])).

cnf(c_2926,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2483,c_1380])).

cnf(c_4417,plain,
    ( k4_xboole_0(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = k1_relat_1(sK3)
    | r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4406,c_2926])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_615,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1147,plain,
    ( v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_615])).

cnf(c_1379,plain,
    ( v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1376,c_1147])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_617,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2018,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1379,c_617])).

cnf(c_3242,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2018,c_874])).

cnf(c_622,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1928,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_622])).

cnf(c_2087,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1928,c_874])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_618,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2093,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2087,c_618])).

cnf(c_3245,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3242,c_2093])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_621,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2092,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2087,c_621])).

cnf(c_2223,plain,
    ( k9_relat_1(sK3,k1_relat_1(sK3)) = k11_relat_1(sK3,sK0) ),
    inference(superposition,[status(thm)],[c_1376,c_2092])).

cnf(c_3443,plain,
    ( k11_relat_1(sK3,sK0) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3245,c_2223])).

cnf(c_4425,plain,
    ( k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) = k1_relat_1(sK3)
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4417,c_1376,c_3443])).

cnf(c_1398,plain,
    ( k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_1376,c_1])).

cnf(c_1406,plain,
    ( k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) != k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_1398,c_1376])).

cnf(c_6247,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4425,c_1406])).

cnf(c_6,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_619,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3445,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3245,c_619])).

cnf(c_3746,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3445,c_874])).

cnf(c_6252,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6247,c_3746])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.56/1.08  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.08  
% 2.56/1.08  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.56/1.08  
% 2.56/1.08  ------  iProver source info
% 2.56/1.08  
% 2.56/1.08  git: date: 2020-06-30 10:37:57 +0100
% 2.56/1.08  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.56/1.08  git: non_committed_changes: false
% 2.56/1.08  git: last_make_outside_of_git: false
% 2.56/1.08  
% 2.56/1.08  ------ 
% 2.56/1.08  ------ Parsing...
% 2.56/1.08  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.56/1.08  
% 2.56/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 2.56/1.08  
% 2.56/1.08  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.56/1.08  
% 2.56/1.08  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.56/1.08  ------ Proving...
% 2.56/1.08  ------ Problem Properties 
% 2.56/1.08  
% 2.56/1.08  
% 2.56/1.08  clauses                                 24
% 2.56/1.08  conjectures                             5
% 2.56/1.08  EPR                                     2
% 2.56/1.08  Horn                                    18
% 2.56/1.08  unary                                   7
% 2.56/1.08  binary                                  8
% 2.56/1.08  lits                                    54
% 2.56/1.08  lits eq                                 20
% 2.56/1.08  fd_pure                                 0
% 2.56/1.08  fd_pseudo                               0
% 2.56/1.08  fd_cond                                 3
% 2.56/1.08  fd_pseudo_cond                          1
% 2.56/1.08  AC symbols                              0
% 2.56/1.08  
% 2.56/1.08  ------ Input Options Time Limit: Unbounded
% 2.56/1.08  
% 2.56/1.08  
% 2.56/1.08  ------ 
% 2.56/1.08  Current options:
% 2.56/1.08  ------ 
% 2.56/1.08  
% 2.56/1.08  
% 2.56/1.08  
% 2.56/1.08  
% 2.56/1.08  ------ Proving...
% 2.56/1.08  
% 2.56/1.08  
% 2.56/1.08  % SZS status Theorem for theBenchmark.p
% 2.56/1.08  
% 2.56/1.08   Resolution empty clause
% 2.56/1.08  
% 2.56/1.08  % SZS output start CNFRefutation for theBenchmark.p
% 2.56/1.08  
% 2.56/1.08  fof(f17,conjecture,(
% 2.56/1.08    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f18,negated_conjecture,(
% 2.56/1.08    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.56/1.08    inference(negated_conjecture,[],[f17])).
% 2.56/1.08  
% 2.56/1.08  fof(f35,plain,(
% 2.56/1.08    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 2.56/1.08    inference(ennf_transformation,[],[f18])).
% 2.56/1.08  
% 2.56/1.08  fof(f36,plain,(
% 2.56/1.08    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 2.56/1.08    inference(flattening,[],[f35])).
% 2.56/1.08  
% 2.56/1.08  fof(f39,plain,(
% 2.56/1.08    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3))),
% 2.56/1.08    introduced(choice_axiom,[])).
% 2.56/1.08  
% 2.56/1.08  fof(f40,plain,(
% 2.56/1.08    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK3,k1_tarski(sK0),sK1) & v1_funct_1(sK3)),
% 2.56/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f39])).
% 2.56/1.08  
% 2.56/1.08  fof(f63,plain,(
% 2.56/1.08    v1_funct_1(sK3)),
% 2.56/1.08    inference(cnf_transformation,[],[f40])).
% 2.56/1.08  
% 2.56/1.08  fof(f5,axiom,(
% 2.56/1.08    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f19,plain,(
% 2.56/1.08    ! [X0,X1] : (~r2_hidden(X1,X0) => k4_xboole_0(X0,k1_tarski(X1)) = X0)),
% 2.56/1.08    inference(unused_predicate_definition_removal,[],[f5])).
% 2.56/1.08  
% 2.56/1.08  fof(f21,plain,(
% 2.56/1.08    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0))),
% 2.56/1.08    inference(ennf_transformation,[],[f19])).
% 2.56/1.08  
% 2.56/1.08  fof(f46,plain,(
% 2.56/1.08    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 2.56/1.08    inference(cnf_transformation,[],[f21])).
% 2.56/1.08  
% 2.56/1.08  fof(f1,axiom,(
% 2.56/1.08    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f41,plain,(
% 2.56/1.08    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.56/1.08    inference(cnf_transformation,[],[f1])).
% 2.56/1.08  
% 2.56/1.08  fof(f2,axiom,(
% 2.56/1.08    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f42,plain,(
% 2.56/1.08    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.56/1.08    inference(cnf_transformation,[],[f2])).
% 2.56/1.08  
% 2.56/1.08  fof(f3,axiom,(
% 2.56/1.08    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f43,plain,(
% 2.56/1.08    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.56/1.08    inference(cnf_transformation,[],[f3])).
% 2.56/1.08  
% 2.56/1.08  fof(f68,plain,(
% 2.56/1.08    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.56/1.08    inference(definition_unfolding,[],[f42,f43])).
% 2.56/1.08  
% 2.56/1.08  fof(f69,plain,(
% 2.56/1.08    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.56/1.08    inference(definition_unfolding,[],[f41,f68])).
% 2.56/1.08  
% 2.56/1.08  fof(f72,plain,(
% 2.56/1.08    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 2.56/1.08    inference(definition_unfolding,[],[f46,f69])).
% 2.56/1.08  
% 2.56/1.08  fof(f12,axiom,(
% 2.56/1.08    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f28,plain,(
% 2.56/1.08    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.56/1.08    inference(ennf_transformation,[],[f12])).
% 2.56/1.08  
% 2.56/1.08  fof(f29,plain,(
% 2.56/1.08    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.56/1.08    inference(flattening,[],[f28])).
% 2.56/1.08  
% 2.56/1.08  fof(f53,plain,(
% 2.56/1.08    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.56/1.08    inference(cnf_transformation,[],[f29])).
% 2.56/1.08  
% 2.56/1.08  fof(f74,plain,(
% 2.56/1.08    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.56/1.08    inference(definition_unfolding,[],[f53,f69])).
% 2.56/1.08  
% 2.56/1.08  fof(f6,axiom,(
% 2.56/1.08    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f22,plain,(
% 2.56/1.08    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.56/1.08    inference(ennf_transformation,[],[f6])).
% 2.56/1.08  
% 2.56/1.08  fof(f47,plain,(
% 2.56/1.08    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.56/1.08    inference(cnf_transformation,[],[f22])).
% 2.56/1.08  
% 2.56/1.08  fof(f65,plain,(
% 2.56/1.08    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.56/1.08    inference(cnf_transformation,[],[f40])).
% 2.56/1.08  
% 2.56/1.08  fof(f76,plain,(
% 2.56/1.08    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.56/1.08    inference(definition_unfolding,[],[f65,f69])).
% 2.56/1.08  
% 2.56/1.08  fof(f8,axiom,(
% 2.56/1.08    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f49,plain,(
% 2.56/1.08    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.56/1.08    inference(cnf_transformation,[],[f8])).
% 2.56/1.08  
% 2.56/1.08  fof(f14,axiom,(
% 2.56/1.08    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f31,plain,(
% 2.56/1.08    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.08    inference(ennf_transformation,[],[f14])).
% 2.56/1.08  
% 2.56/1.08  fof(f55,plain,(
% 2.56/1.08    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.08    inference(cnf_transformation,[],[f31])).
% 2.56/1.08  
% 2.56/1.08  fof(f16,axiom,(
% 2.56/1.08    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f33,plain,(
% 2.56/1.08    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.08    inference(ennf_transformation,[],[f16])).
% 2.56/1.08  
% 2.56/1.08  fof(f34,plain,(
% 2.56/1.08    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.08    inference(flattening,[],[f33])).
% 2.56/1.08  
% 2.56/1.08  fof(f38,plain,(
% 2.56/1.08    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.08    inference(nnf_transformation,[],[f34])).
% 2.56/1.08  
% 2.56/1.08  fof(f57,plain,(
% 2.56/1.08    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.08    inference(cnf_transformation,[],[f38])).
% 2.56/1.08  
% 2.56/1.08  fof(f64,plain,(
% 2.56/1.08    v1_funct_2(sK3,k1_tarski(sK0),sK1)),
% 2.56/1.08    inference(cnf_transformation,[],[f40])).
% 2.56/1.08  
% 2.56/1.08  fof(f77,plain,(
% 2.56/1.08    v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.56/1.08    inference(definition_unfolding,[],[f64,f69])).
% 2.56/1.08  
% 2.56/1.08  fof(f66,plain,(
% 2.56/1.08    k1_xboole_0 != sK1),
% 2.56/1.08    inference(cnf_transformation,[],[f40])).
% 2.56/1.08  
% 2.56/1.08  fof(f4,axiom,(
% 2.56/1.08    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f37,plain,(
% 2.56/1.08    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 2.56/1.08    inference(nnf_transformation,[],[f4])).
% 2.56/1.08  
% 2.56/1.08  fof(f44,plain,(
% 2.56/1.08    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.56/1.08    inference(cnf_transformation,[],[f37])).
% 2.56/1.08  
% 2.56/1.08  fof(f71,plain,(
% 2.56/1.08    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 2.56/1.08    inference(definition_unfolding,[],[f44,f69,f69,f69])).
% 2.56/1.08  
% 2.56/1.08  fof(f78,plain,(
% 2.56/1.08    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 2.56/1.08    inference(equality_resolution,[],[f71])).
% 2.56/1.08  
% 2.56/1.08  fof(f45,plain,(
% 2.56/1.08    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 2.56/1.08    inference(cnf_transformation,[],[f37])).
% 2.56/1.08  
% 2.56/1.08  fof(f70,plain,(
% 2.56/1.08    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 2.56/1.08    inference(definition_unfolding,[],[f45,f69,f69,f69])).
% 2.56/1.08  
% 2.56/1.08  fof(f15,axiom,(
% 2.56/1.08    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f32,plain,(
% 2.56/1.08    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.08    inference(ennf_transformation,[],[f15])).
% 2.56/1.08  
% 2.56/1.08  fof(f56,plain,(
% 2.56/1.08    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.08    inference(cnf_transformation,[],[f32])).
% 2.56/1.08  
% 2.56/1.08  fof(f67,plain,(
% 2.56/1.08    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.56/1.08    inference(cnf_transformation,[],[f40])).
% 2.56/1.08  
% 2.56/1.08  fof(f75,plain,(
% 2.56/1.08    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.56/1.08    inference(definition_unfolding,[],[f67,f69,f69])).
% 2.56/1.08  
% 2.56/1.08  fof(f13,axiom,(
% 2.56/1.08    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f20,plain,(
% 2.56/1.08    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.56/1.08    inference(pure_predicate_removal,[],[f13])).
% 2.56/1.08  
% 2.56/1.08  fof(f30,plain,(
% 2.56/1.08    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.08    inference(ennf_transformation,[],[f20])).
% 2.56/1.08  
% 2.56/1.08  fof(f54,plain,(
% 2.56/1.08    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.08    inference(cnf_transformation,[],[f30])).
% 2.56/1.08  
% 2.56/1.08  fof(f11,axiom,(
% 2.56/1.08    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f26,plain,(
% 2.56/1.08    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.56/1.08    inference(ennf_transformation,[],[f11])).
% 2.56/1.08  
% 2.56/1.08  fof(f27,plain,(
% 2.56/1.08    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.56/1.08    inference(flattening,[],[f26])).
% 2.56/1.08  
% 2.56/1.08  fof(f52,plain,(
% 2.56/1.08    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.56/1.08    inference(cnf_transformation,[],[f27])).
% 2.56/1.08  
% 2.56/1.08  fof(f10,axiom,(
% 2.56/1.08    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f25,plain,(
% 2.56/1.08    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.56/1.08    inference(ennf_transformation,[],[f10])).
% 2.56/1.08  
% 2.56/1.08  fof(f51,plain,(
% 2.56/1.08    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.56/1.08    inference(cnf_transformation,[],[f25])).
% 2.56/1.08  
% 2.56/1.08  fof(f7,axiom,(
% 2.56/1.08    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f23,plain,(
% 2.56/1.08    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.56/1.08    inference(ennf_transformation,[],[f7])).
% 2.56/1.08  
% 2.56/1.08  fof(f48,plain,(
% 2.56/1.08    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.56/1.08    inference(cnf_transformation,[],[f23])).
% 2.56/1.08  
% 2.56/1.08  fof(f73,plain,(
% 2.56/1.08    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.56/1.08    inference(definition_unfolding,[],[f48,f69])).
% 2.56/1.08  
% 2.56/1.08  fof(f9,axiom,(
% 2.56/1.08    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))))),
% 2.56/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.08  
% 2.56/1.08  fof(f24,plain,(
% 2.56/1.08    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.56/1.08    inference(ennf_transformation,[],[f9])).
% 2.56/1.08  
% 2.56/1.08  fof(f50,plain,(
% 2.56/1.08    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 2.56/1.08    inference(cnf_transformation,[],[f24])).
% 2.56/1.08  
% 2.56/1.08  cnf(c_23,negated_conjecture,
% 2.56/1.08      ( v1_funct_1(sK3) ),
% 2.56/1.08      inference(cnf_transformation,[],[f63]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_603,plain,
% 2.56/1.08      ( v1_funct_1(sK3) = iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_2,plain,
% 2.56/1.08      ( r2_hidden(X0,X1) | k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) = X1 ),
% 2.56/1.08      inference(cnf_transformation,[],[f72]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_623,plain,
% 2.56/1.08      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0
% 2.56/1.08      | r2_hidden(X1,X0) = iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_9,plain,
% 2.56/1.08      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.56/1.08      | ~ v1_funct_1(X1)
% 2.56/1.08      | ~ v1_relat_1(X1)
% 2.56/1.08      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 2.56/1.08      inference(cnf_transformation,[],[f74]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_616,plain,
% 2.56/1.08      ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k11_relat_1(X0,X1)
% 2.56/1.08      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 2.56/1.08      | v1_funct_1(X0) != iProver_top
% 2.56/1.08      | v1_relat_1(X0) != iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_3741,plain,
% 2.56/1.08      ( k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k11_relat_1(X0,X1)
% 2.56/1.08      | k4_xboole_0(k1_relat_1(X0),k2_enumset1(X1,X1,X1,X1)) = k1_relat_1(X0)
% 2.56/1.08      | v1_funct_1(X0) != iProver_top
% 2.56/1.08      | v1_relat_1(X0) != iProver_top ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_623,c_616]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_4108,plain,
% 2.56/1.08      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.56/1.08      | k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3)
% 2.56/1.08      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_603,c_3741]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_3,plain,
% 2.56/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.56/1.08      inference(cnf_transformation,[],[f47]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_21,negated_conjecture,
% 2.56/1.08      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.56/1.08      inference(cnf_transformation,[],[f76]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_846,plain,
% 2.56/1.08      ( ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.56/1.08      | v1_relat_1(sK3) ),
% 2.56/1.08      inference(resolution,[status(thm)],[c_3,c_21]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_5,plain,
% 2.56/1.08      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.56/1.08      inference(cnf_transformation,[],[f49]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_873,plain,
% 2.56/1.08      ( v1_relat_1(sK3) ),
% 2.56/1.08      inference(forward_subsumption_resolution,[status(thm)],[c_846,c_5]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_874,plain,
% 2.56/1.08      ( v1_relat_1(sK3) = iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_873]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_4405,plain,
% 2.56/1.08      ( k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3)
% 2.56/1.08      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 2.56/1.08      inference(global_propositional_subsumption,[status(thm)],[c_4108,c_874]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_4406,plain,
% 2.56/1.08      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 2.56/1.08      | k4_xboole_0(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) = k1_relat_1(sK3) ),
% 2.56/1.08      inference(renaming,[status(thm)],[c_4405]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_605,plain,
% 2.56/1.08      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_11,plain,
% 2.56/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.08      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.56/1.08      inference(cnf_transformation,[],[f55]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_614,plain,
% 2.56/1.08      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.56/1.08      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_1328,plain,
% 2.56/1.08      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_605,c_614]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_18,plain,
% 2.56/1.08      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.08      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.08      | k1_relset_1(X1,X2,X0) = X1
% 2.56/1.08      | k1_xboole_0 = X2 ),
% 2.56/1.08      inference(cnf_transformation,[],[f57]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_607,plain,
% 2.56/1.08      ( k1_relset_1(X0,X1,X2) = X0
% 2.56/1.08      | k1_xboole_0 = X1
% 2.56/1.08      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.56/1.08      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_1014,plain,
% 2.56/1.08      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0)
% 2.56/1.08      | sK1 = k1_xboole_0
% 2.56/1.08      | v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) != iProver_top ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_605,c_607]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_22,negated_conjecture,
% 2.56/1.08      ( v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 2.56/1.08      inference(cnf_transformation,[],[f77]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_25,plain,
% 2.56/1.08      ( v1_funct_2(sK3,k2_enumset1(sK0,sK0,sK0,sK0),sK1) = iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_20,negated_conjecture,
% 2.56/1.08      ( k1_xboole_0 != sK1 ),
% 2.56/1.08      inference(cnf_transformation,[],[f66]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_1,plain,
% 2.56/1.08      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 2.56/1.08      inference(cnf_transformation,[],[f78]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_77,plain,
% 2.56/1.08      ( k4_xboole_0(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
% 2.56/1.08      inference(instantiation,[status(thm)],[c_1]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_0,plain,
% 2.56/1.08      ( X0 = X1
% 2.56/1.08      | k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = k2_enumset1(X1,X1,X1,X1) ),
% 2.56/1.08      inference(cnf_transformation,[],[f70]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_78,plain,
% 2.56/1.08      ( k4_xboole_0(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
% 2.56/1.08      | k1_xboole_0 = k1_xboole_0 ),
% 2.56/1.08      inference(instantiation,[status(thm)],[c_0]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_211,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_828,plain,
% 2.56/1.08      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.56/1.08      inference(instantiation,[status(thm)],[c_211]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_829,plain,
% 2.56/1.08      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 2.56/1.08      inference(instantiation,[status(thm)],[c_828]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_1261,plain,
% 2.56/1.08      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 2.56/1.08      inference(global_propositional_subsumption,
% 2.56/1.08                [status(thm)],
% 2.56/1.08                [c_1014,c_25,c_20,c_77,c_78,c_829]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_1376,plain,
% 2.56/1.08      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
% 2.56/1.08      inference(demodulation,[status(thm)],[c_1328,c_1261]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_1381,plain,
% 2.56/1.08      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 2.56/1.08      inference(demodulation,[status(thm)],[c_1376,c_605]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_12,plain,
% 2.56/1.08      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.08      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.56/1.08      inference(cnf_transformation,[],[f56]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_613,plain,
% 2.56/1.08      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.56/1.08      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_2483,plain,
% 2.56/1.08      ( k7_relset_1(k1_relat_1(sK3),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_1381,c_613]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_19,negated_conjecture,
% 2.56/1.08      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.56/1.08      inference(cnf_transformation,[],[f75]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_606,plain,
% 2.56/1.08      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_1380,plain,
% 2.56/1.08      ( r1_tarski(k7_relset_1(k1_relat_1(sK3),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.56/1.08      inference(demodulation,[status(thm)],[c_1376,c_606]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_2926,plain,
% 2.56/1.08      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.56/1.08      inference(demodulation,[status(thm)],[c_2483,c_1380]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_4417,plain,
% 2.56/1.08      ( k4_xboole_0(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = k1_relat_1(sK3)
% 2.56/1.08      | r1_tarski(k9_relat_1(sK3,sK2),k11_relat_1(sK3,sK0)) != iProver_top ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_4406,c_2926]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_10,plain,
% 2.56/1.08      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.56/1.08      inference(cnf_transformation,[],[f54]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_615,plain,
% 2.56/1.08      ( v4_relat_1(X0,X1) = iProver_top
% 2.56/1.08      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_1147,plain,
% 2.56/1.08      ( v4_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_605,c_615]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_1379,plain,
% 2.56/1.08      ( v4_relat_1(sK3,k1_relat_1(sK3)) = iProver_top ),
% 2.56/1.08      inference(demodulation,[status(thm)],[c_1376,c_1147]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_8,plain,
% 2.56/1.08      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.56/1.08      inference(cnf_transformation,[],[f52]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_617,plain,
% 2.56/1.08      ( k7_relat_1(X0,X1) = X0
% 2.56/1.08      | v4_relat_1(X0,X1) != iProver_top
% 2.56/1.08      | v1_relat_1(X0) != iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_2018,plain,
% 2.56/1.08      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3
% 2.56/1.08      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_1379,c_617]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_3242,plain,
% 2.56/1.08      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 2.56/1.08      inference(global_propositional_subsumption,[status(thm)],[c_2018,c_874]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_622,plain,
% 2.56/1.08      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.56/1.08      | v1_relat_1(X1) != iProver_top
% 2.56/1.08      | v1_relat_1(X0) = iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_1928,plain,
% 2.56/1.08      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) != iProver_top
% 2.56/1.08      | v1_relat_1(sK3) = iProver_top ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_1381,c_622]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_2087,plain,
% 2.56/1.08      ( v1_relat_1(sK3) = iProver_top ),
% 2.56/1.08      inference(global_propositional_subsumption,[status(thm)],[c_1928,c_874]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_7,plain,
% 2.56/1.08      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.56/1.08      inference(cnf_transformation,[],[f51]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_618,plain,
% 2.56/1.08      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.56/1.08      | v1_relat_1(X0) != iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_2093,plain,
% 2.56/1.08      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_2087,c_618]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_3245,plain,
% 2.56/1.08      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k2_relat_1(sK3) ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_3242,c_2093]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_4,plain,
% 2.56/1.08      ( ~ v1_relat_1(X0)
% 2.56/1.08      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.56/1.08      inference(cnf_transformation,[],[f73]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_621,plain,
% 2.56/1.08      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.56/1.08      | v1_relat_1(X0) != iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_2092,plain,
% 2.56/1.08      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_2087,c_621]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_2223,plain,
% 2.56/1.08      ( k9_relat_1(sK3,k1_relat_1(sK3)) = k11_relat_1(sK3,sK0) ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_1376,c_2092]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_3443,plain,
% 2.56/1.08      ( k11_relat_1(sK3,sK0) = k2_relat_1(sK3) ),
% 2.56/1.08      inference(demodulation,[status(thm)],[c_3245,c_2223]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_4425,plain,
% 2.56/1.08      ( k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) = k1_relat_1(sK3)
% 2.56/1.08      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 2.56/1.08      inference(light_normalisation,[status(thm)],[c_4417,c_1376,c_3443]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_1398,plain,
% 2.56/1.08      ( k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_1376,c_1]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_1406,plain,
% 2.56/1.08      ( k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)) != k1_relat_1(sK3) ),
% 2.56/1.08      inference(light_normalisation,[status(thm)],[c_1398,c_1376]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_6247,plain,
% 2.56/1.08      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 2.56/1.08      inference(global_propositional_subsumption,[status(thm)],[c_4425,c_1406]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_6,plain,
% 2.56/1.08      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0)))
% 2.56/1.08      | ~ v1_relat_1(X0) ),
% 2.56/1.08      inference(cnf_transformation,[],[f50]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_619,plain,
% 2.56/1.08      ( r1_tarski(k9_relat_1(X0,X1),k9_relat_1(X0,k1_relat_1(X0))) = iProver_top
% 2.56/1.08      | v1_relat_1(X0) != iProver_top ),
% 2.56/1.08      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_3445,plain,
% 2.56/1.08      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) = iProver_top
% 2.56/1.08      | v1_relat_1(sK3) != iProver_top ),
% 2.56/1.08      inference(superposition,[status(thm)],[c_3245,c_619]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_3746,plain,
% 2.56/1.08      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 2.56/1.08      inference(global_propositional_subsumption,[status(thm)],[c_3445,c_874]) ).
% 2.56/1.08  
% 2.56/1.08  cnf(c_6252,plain,
% 2.56/1.08      ( $false ),
% 2.56/1.08      inference(forward_subsumption_resolution,[status(thm)],[c_6247,c_3746]) ).
% 2.56/1.08  
% 2.56/1.08  
% 2.56/1.08  % SZS output end CNFRefutation for theBenchmark.p
% 2.56/1.08  
% 2.56/1.08  ------                               Statistics
% 2.56/1.08  
% 2.56/1.08  ------ Selected
% 2.56/1.08  
% 2.56/1.08  total_time:                             0.513
% 2.56/1.08  
%------------------------------------------------------------------------------
