%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:15 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  162 (1608 expanded)
%              Number of clauses        :   89 ( 331 expanded)
%              Number of leaves         :   24 ( 431 expanded)
%              Depth                    :   27
%              Number of atoms          :  474 (4249 expanded)
%              Number of equality atoms :  290 (2448 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f41,plain,
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

fof(f42,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f41])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f79])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f76,f80])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f36])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f47,f46,f79,f79,f79,f80,f80,f80,f46])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f39])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f75,f80])).

fof(f74,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(definition_unfolding,[],[f78,f80,f80])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f65,f80,f80])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_13,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_345,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_346,plain,
    ( v4_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_412,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_346])).

cnf(c_413,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_357,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_358,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_417,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_358])).

cnf(c_1907,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_2205,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1907])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1920,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2993,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2205,c_1920])).

cnf(c_26,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1911,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK1,sK1,sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_316,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_320,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_32,c_30,c_29])).

cnf(c_1909,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_336,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_337,plain,
    ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_2108,plain,
    ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_337])).

cnf(c_2150,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1909,c_2108])).

cnf(c_2516,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1911,c_2150])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1914,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2761,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2516,c_1914])).

cnf(c_3191,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2993,c_2761])).

cnf(c_33,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1495,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2087,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_2090,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_2091,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2090])).

cnf(c_28,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2133,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2108,c_28])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1915,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3185,plain,
    ( k2_enumset1(k1_funct_1(X0,sK1),k1_funct_1(X0,sK1),k1_funct_1(X0,sK1),k1_funct_1(X0,sK1)) = k2_relat_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2993,c_1915])).

cnf(c_3767,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3185])).

cnf(c_3820,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3191,c_33,c_2087,c_2091,c_2133,c_3767])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1918,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3833,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3820,c_1918])).

cnf(c_2176,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2616,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_1496,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2429,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_2926,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2429])).

cnf(c_2928,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2926])).

cnf(c_3836,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3833,c_33,c_2087,c_2090,c_2091,c_2133,c_2176,c_2616,c_2928,c_3767])).

cnf(c_3840,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK1,sK1,sK1,sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3836,c_2761])).

cnf(c_12,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3871,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK1,sK1,sK1,sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3840,c_12])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1929,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4069,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3871,c_1929])).

cnf(c_4095,plain,
    ( k2_enumset1(k1_funct_1(X0,sK1),k1_funct_1(X0,sK1),k1_funct_1(X0,sK1),k1_funct_1(X0,sK1)) = k2_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4069,c_1915])).

cnf(c_4254,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) = k2_relat_1(k1_xboole_0)
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_4095])).

cnf(c_4255,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) = k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4254,c_12])).

cnf(c_3844,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) != k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3836,c_2133])).

cnf(c_3857,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3844,c_12])).

cnf(c_2245,plain,
    ( X0 != X1
    | X0 = k6_relat_1(X2)
    | k6_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_2246,plain,
    ( k6_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2245])).

cnf(c_1500,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2127,plain,
    ( v1_relat_1(X0)
    | ~ v1_relat_1(k6_relat_1(X1))
    | X0 != k6_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1500])).

cnf(c_2128,plain,
    ( X0 != k6_relat_1(X1)
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2127])).

cnf(c_2130,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | v1_relat_1(k6_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2128])).

cnf(c_1503,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2109,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k6_relat_1(X1))
    | X0 != k6_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_2110,plain,
    ( X0 != k6_relat_1(X1)
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(k6_relat_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2109])).

cnf(c_2112,plain,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | v1_funct_1(k6_relat_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2110])).

cnf(c_1522,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_16,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_17,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_64,plain,
    ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_66,plain,
    ( v1_funct_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_18,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_61,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_63,plain,
    ( v1_relat_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4255,c_3857,c_2246,c_2130,c_2112,c_1522,c_16,c_66,c_63])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:51:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.98/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.02  
% 1.98/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.98/1.02  
% 1.98/1.02  ------  iProver source info
% 1.98/1.02  
% 1.98/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.98/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.98/1.02  git: non_committed_changes: false
% 1.98/1.02  git: last_make_outside_of_git: false
% 1.98/1.02  
% 1.98/1.02  ------ 
% 1.98/1.02  
% 1.98/1.02  ------ Input Options
% 1.98/1.02  
% 1.98/1.02  --out_options                           all
% 1.98/1.02  --tptp_safe_out                         true
% 1.98/1.02  --problem_path                          ""
% 1.98/1.02  --include_path                          ""
% 1.98/1.02  --clausifier                            res/vclausify_rel
% 1.98/1.02  --clausifier_options                    --mode clausify
% 1.98/1.02  --stdin                                 false
% 1.98/1.02  --stats_out                             all
% 1.98/1.02  
% 1.98/1.02  ------ General Options
% 1.98/1.02  
% 1.98/1.02  --fof                                   false
% 1.98/1.02  --time_out_real                         305.
% 1.98/1.02  --time_out_virtual                      -1.
% 1.98/1.02  --symbol_type_check                     false
% 1.98/1.02  --clausify_out                          false
% 1.98/1.02  --sig_cnt_out                           false
% 1.98/1.02  --trig_cnt_out                          false
% 1.98/1.02  --trig_cnt_out_tolerance                1.
% 1.98/1.02  --trig_cnt_out_sk_spl                   false
% 1.98/1.02  --abstr_cl_out                          false
% 1.98/1.02  
% 1.98/1.02  ------ Global Options
% 1.98/1.02  
% 1.98/1.02  --schedule                              default
% 1.98/1.02  --add_important_lit                     false
% 1.98/1.02  --prop_solver_per_cl                    1000
% 1.98/1.02  --min_unsat_core                        false
% 1.98/1.02  --soft_assumptions                      false
% 1.98/1.02  --soft_lemma_size                       3
% 1.98/1.02  --prop_impl_unit_size                   0
% 1.98/1.02  --prop_impl_unit                        []
% 1.98/1.02  --share_sel_clauses                     true
% 1.98/1.02  --reset_solvers                         false
% 1.98/1.02  --bc_imp_inh                            [conj_cone]
% 1.98/1.02  --conj_cone_tolerance                   3.
% 1.98/1.02  --extra_neg_conj                        none
% 1.98/1.02  --large_theory_mode                     true
% 1.98/1.02  --prolific_symb_bound                   200
% 1.98/1.02  --lt_threshold                          2000
% 1.98/1.02  --clause_weak_htbl                      true
% 1.98/1.02  --gc_record_bc_elim                     false
% 1.98/1.02  
% 1.98/1.02  ------ Preprocessing Options
% 1.98/1.02  
% 1.98/1.02  --preprocessing_flag                    true
% 1.98/1.02  --time_out_prep_mult                    0.1
% 1.98/1.02  --splitting_mode                        input
% 1.98/1.02  --splitting_grd                         true
% 1.98/1.02  --splitting_cvd                         false
% 1.98/1.02  --splitting_cvd_svl                     false
% 1.98/1.02  --splitting_nvd                         32
% 1.98/1.02  --sub_typing                            true
% 1.98/1.02  --prep_gs_sim                           true
% 1.98/1.02  --prep_unflatten                        true
% 1.98/1.02  --prep_res_sim                          true
% 1.98/1.02  --prep_upred                            true
% 1.98/1.02  --prep_sem_filter                       exhaustive
% 1.98/1.02  --prep_sem_filter_out                   false
% 1.98/1.02  --pred_elim                             true
% 1.98/1.02  --res_sim_input                         true
% 1.98/1.02  --eq_ax_congr_red                       true
% 1.98/1.02  --pure_diseq_elim                       true
% 1.98/1.02  --brand_transform                       false
% 1.98/1.02  --non_eq_to_eq                          false
% 1.98/1.02  --prep_def_merge                        true
% 1.98/1.02  --prep_def_merge_prop_impl              false
% 1.98/1.02  --prep_def_merge_mbd                    true
% 1.98/1.02  --prep_def_merge_tr_red                 false
% 1.98/1.02  --prep_def_merge_tr_cl                  false
% 1.98/1.02  --smt_preprocessing                     true
% 1.98/1.02  --smt_ac_axioms                         fast
% 1.98/1.02  --preprocessed_out                      false
% 1.98/1.02  --preprocessed_stats                    false
% 1.98/1.02  
% 1.98/1.02  ------ Abstraction refinement Options
% 1.98/1.02  
% 1.98/1.02  --abstr_ref                             []
% 1.98/1.02  --abstr_ref_prep                        false
% 1.98/1.02  --abstr_ref_until_sat                   false
% 1.98/1.02  --abstr_ref_sig_restrict                funpre
% 1.98/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.98/1.02  --abstr_ref_under                       []
% 1.98/1.02  
% 1.98/1.02  ------ SAT Options
% 1.98/1.02  
% 1.98/1.02  --sat_mode                              false
% 1.98/1.02  --sat_fm_restart_options                ""
% 1.98/1.02  --sat_gr_def                            false
% 1.98/1.02  --sat_epr_types                         true
% 1.98/1.02  --sat_non_cyclic_types                  false
% 1.98/1.02  --sat_finite_models                     false
% 1.98/1.02  --sat_fm_lemmas                         false
% 1.98/1.02  --sat_fm_prep                           false
% 1.98/1.02  --sat_fm_uc_incr                        true
% 1.98/1.02  --sat_out_model                         small
% 1.98/1.02  --sat_out_clauses                       false
% 1.98/1.02  
% 1.98/1.02  ------ QBF Options
% 1.98/1.02  
% 1.98/1.02  --qbf_mode                              false
% 1.98/1.02  --qbf_elim_univ                         false
% 1.98/1.02  --qbf_dom_inst                          none
% 1.98/1.02  --qbf_dom_pre_inst                      false
% 1.98/1.02  --qbf_sk_in                             false
% 1.98/1.02  --qbf_pred_elim                         true
% 1.98/1.02  --qbf_split                             512
% 1.98/1.02  
% 1.98/1.02  ------ BMC1 Options
% 1.98/1.02  
% 1.98/1.02  --bmc1_incremental                      false
% 1.98/1.02  --bmc1_axioms                           reachable_all
% 1.98/1.02  --bmc1_min_bound                        0
% 1.98/1.02  --bmc1_max_bound                        -1
% 1.98/1.02  --bmc1_max_bound_default                -1
% 1.98/1.02  --bmc1_symbol_reachability              true
% 1.98/1.02  --bmc1_property_lemmas                  false
% 1.98/1.02  --bmc1_k_induction                      false
% 1.98/1.02  --bmc1_non_equiv_states                 false
% 1.98/1.02  --bmc1_deadlock                         false
% 1.98/1.02  --bmc1_ucm                              false
% 1.98/1.02  --bmc1_add_unsat_core                   none
% 1.98/1.02  --bmc1_unsat_core_children              false
% 1.98/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.98/1.02  --bmc1_out_stat                         full
% 1.98/1.02  --bmc1_ground_init                      false
% 1.98/1.02  --bmc1_pre_inst_next_state              false
% 1.98/1.02  --bmc1_pre_inst_state                   false
% 1.98/1.02  --bmc1_pre_inst_reach_state             false
% 1.98/1.02  --bmc1_out_unsat_core                   false
% 1.98/1.02  --bmc1_aig_witness_out                  false
% 1.98/1.02  --bmc1_verbose                          false
% 1.98/1.02  --bmc1_dump_clauses_tptp                false
% 1.98/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.98/1.02  --bmc1_dump_file                        -
% 1.98/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.98/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.98/1.02  --bmc1_ucm_extend_mode                  1
% 1.98/1.02  --bmc1_ucm_init_mode                    2
% 1.98/1.02  --bmc1_ucm_cone_mode                    none
% 1.98/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.98/1.02  --bmc1_ucm_relax_model                  4
% 1.98/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.98/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.98/1.02  --bmc1_ucm_layered_model                none
% 1.98/1.02  --bmc1_ucm_max_lemma_size               10
% 1.98/1.02  
% 1.98/1.02  ------ AIG Options
% 1.98/1.02  
% 1.98/1.02  --aig_mode                              false
% 1.98/1.02  
% 1.98/1.02  ------ Instantiation Options
% 1.98/1.02  
% 1.98/1.02  --instantiation_flag                    true
% 1.98/1.02  --inst_sos_flag                         false
% 1.98/1.02  --inst_sos_phase                        true
% 1.98/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.98/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.98/1.02  --inst_lit_sel_side                     num_symb
% 1.98/1.02  --inst_solver_per_active                1400
% 1.98/1.02  --inst_solver_calls_frac                1.
% 1.98/1.02  --inst_passive_queue_type               priority_queues
% 1.98/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.98/1.02  --inst_passive_queues_freq              [25;2]
% 1.98/1.02  --inst_dismatching                      true
% 1.98/1.02  --inst_eager_unprocessed_to_passive     true
% 1.98/1.02  --inst_prop_sim_given                   true
% 1.98/1.02  --inst_prop_sim_new                     false
% 1.98/1.02  --inst_subs_new                         false
% 1.98/1.02  --inst_eq_res_simp                      false
% 1.98/1.02  --inst_subs_given                       false
% 1.98/1.02  --inst_orphan_elimination               true
% 1.98/1.02  --inst_learning_loop_flag               true
% 1.98/1.02  --inst_learning_start                   3000
% 1.98/1.02  --inst_learning_factor                  2
% 1.98/1.02  --inst_start_prop_sim_after_learn       3
% 1.98/1.02  --inst_sel_renew                        solver
% 1.98/1.02  --inst_lit_activity_flag                true
% 1.98/1.02  --inst_restr_to_given                   false
% 1.98/1.02  --inst_activity_threshold               500
% 1.98/1.02  --inst_out_proof                        true
% 1.98/1.02  
% 1.98/1.02  ------ Resolution Options
% 1.98/1.02  
% 1.98/1.02  --resolution_flag                       true
% 1.98/1.02  --res_lit_sel                           adaptive
% 1.98/1.02  --res_lit_sel_side                      none
% 1.98/1.02  --res_ordering                          kbo
% 1.98/1.02  --res_to_prop_solver                    active
% 1.98/1.02  --res_prop_simpl_new                    false
% 1.98/1.02  --res_prop_simpl_given                  true
% 1.98/1.02  --res_passive_queue_type                priority_queues
% 1.98/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.98/1.02  --res_passive_queues_freq               [15;5]
% 1.98/1.02  --res_forward_subs                      full
% 1.98/1.02  --res_backward_subs                     full
% 1.98/1.02  --res_forward_subs_resolution           true
% 1.98/1.02  --res_backward_subs_resolution          true
% 1.98/1.02  --res_orphan_elimination                true
% 1.98/1.02  --res_time_limit                        2.
% 1.98/1.02  --res_out_proof                         true
% 1.98/1.02  
% 1.98/1.02  ------ Superposition Options
% 1.98/1.02  
% 1.98/1.02  --superposition_flag                    true
% 1.98/1.02  --sup_passive_queue_type                priority_queues
% 1.98/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.98/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.98/1.02  --demod_completeness_check              fast
% 1.98/1.02  --demod_use_ground                      true
% 1.98/1.02  --sup_to_prop_solver                    passive
% 1.98/1.02  --sup_prop_simpl_new                    true
% 1.98/1.02  --sup_prop_simpl_given                  true
% 1.98/1.02  --sup_fun_splitting                     false
% 1.98/1.02  --sup_smt_interval                      50000
% 1.98/1.02  
% 1.98/1.02  ------ Superposition Simplification Setup
% 1.98/1.02  
% 1.98/1.02  --sup_indices_passive                   []
% 1.98/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.98/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/1.02  --sup_full_bw                           [BwDemod]
% 1.98/1.02  --sup_immed_triv                        [TrivRules]
% 1.98/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.98/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/1.02  --sup_immed_bw_main                     []
% 1.98/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.98/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/1.02  
% 1.98/1.02  ------ Combination Options
% 1.98/1.02  
% 1.98/1.02  --comb_res_mult                         3
% 1.98/1.02  --comb_sup_mult                         2
% 1.98/1.02  --comb_inst_mult                        10
% 1.98/1.02  
% 1.98/1.02  ------ Debug Options
% 1.98/1.02  
% 1.98/1.02  --dbg_backtrace                         false
% 1.98/1.02  --dbg_dump_prop_clauses                 false
% 1.98/1.02  --dbg_dump_prop_clauses_file            -
% 1.98/1.02  --dbg_out_stat                          false
% 1.98/1.02  ------ Parsing...
% 1.98/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.98/1.02  
% 1.98/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.98/1.02  
% 1.98/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.98/1.02  
% 1.98/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.98/1.02  ------ Proving...
% 1.98/1.02  ------ Problem Properties 
% 1.98/1.02  
% 1.98/1.02  
% 1.98/1.02  clauses                                 29
% 1.98/1.02  conjectures                             3
% 1.98/1.02  EPR                                     4
% 1.98/1.02  Horn                                    27
% 1.98/1.02  unary                                   17
% 1.98/1.02  binary                                  6
% 1.98/1.02  lits                                    54
% 1.98/1.02  lits eq                                 28
% 1.98/1.02  fd_pure                                 0
% 1.98/1.02  fd_pseudo                               0
% 1.98/1.02  fd_cond                                 5
% 1.98/1.02  fd_pseudo_cond                          1
% 1.98/1.02  AC symbols                              0
% 1.98/1.02  
% 1.98/1.02  ------ Schedule dynamic 5 is on 
% 1.98/1.02  
% 1.98/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.98/1.02  
% 1.98/1.02  
% 1.98/1.02  ------ 
% 1.98/1.02  Current options:
% 1.98/1.02  ------ 
% 1.98/1.02  
% 1.98/1.02  ------ Input Options
% 1.98/1.02  
% 1.98/1.02  --out_options                           all
% 1.98/1.02  --tptp_safe_out                         true
% 1.98/1.02  --problem_path                          ""
% 1.98/1.02  --include_path                          ""
% 1.98/1.02  --clausifier                            res/vclausify_rel
% 1.98/1.02  --clausifier_options                    --mode clausify
% 1.98/1.02  --stdin                                 false
% 1.98/1.02  --stats_out                             all
% 1.98/1.02  
% 1.98/1.02  ------ General Options
% 1.98/1.02  
% 1.98/1.02  --fof                                   false
% 1.98/1.02  --time_out_real                         305.
% 1.98/1.02  --time_out_virtual                      -1.
% 1.98/1.02  --symbol_type_check                     false
% 1.98/1.02  --clausify_out                          false
% 1.98/1.02  --sig_cnt_out                           false
% 1.98/1.02  --trig_cnt_out                          false
% 1.98/1.02  --trig_cnt_out_tolerance                1.
% 1.98/1.02  --trig_cnt_out_sk_spl                   false
% 1.98/1.02  --abstr_cl_out                          false
% 1.98/1.02  
% 1.98/1.02  ------ Global Options
% 1.98/1.02  
% 1.98/1.02  --schedule                              default
% 1.98/1.02  --add_important_lit                     false
% 1.98/1.02  --prop_solver_per_cl                    1000
% 1.98/1.02  --min_unsat_core                        false
% 1.98/1.02  --soft_assumptions                      false
% 1.98/1.02  --soft_lemma_size                       3
% 1.98/1.02  --prop_impl_unit_size                   0
% 1.98/1.02  --prop_impl_unit                        []
% 1.98/1.02  --share_sel_clauses                     true
% 1.98/1.02  --reset_solvers                         false
% 1.98/1.02  --bc_imp_inh                            [conj_cone]
% 1.98/1.02  --conj_cone_tolerance                   3.
% 1.98/1.02  --extra_neg_conj                        none
% 1.98/1.02  --large_theory_mode                     true
% 1.98/1.02  --prolific_symb_bound                   200
% 1.98/1.02  --lt_threshold                          2000
% 1.98/1.02  --clause_weak_htbl                      true
% 1.98/1.02  --gc_record_bc_elim                     false
% 1.98/1.02  
% 1.98/1.02  ------ Preprocessing Options
% 1.98/1.02  
% 1.98/1.02  --preprocessing_flag                    true
% 1.98/1.02  --time_out_prep_mult                    0.1
% 1.98/1.02  --splitting_mode                        input
% 1.98/1.02  --splitting_grd                         true
% 1.98/1.02  --splitting_cvd                         false
% 1.98/1.02  --splitting_cvd_svl                     false
% 1.98/1.02  --splitting_nvd                         32
% 1.98/1.02  --sub_typing                            true
% 1.98/1.02  --prep_gs_sim                           true
% 1.98/1.02  --prep_unflatten                        true
% 1.98/1.02  --prep_res_sim                          true
% 1.98/1.02  --prep_upred                            true
% 1.98/1.02  --prep_sem_filter                       exhaustive
% 1.98/1.02  --prep_sem_filter_out                   false
% 1.98/1.02  --pred_elim                             true
% 1.98/1.02  --res_sim_input                         true
% 1.98/1.02  --eq_ax_congr_red                       true
% 1.98/1.02  --pure_diseq_elim                       true
% 1.98/1.02  --brand_transform                       false
% 1.98/1.02  --non_eq_to_eq                          false
% 1.98/1.02  --prep_def_merge                        true
% 1.98/1.02  --prep_def_merge_prop_impl              false
% 1.98/1.02  --prep_def_merge_mbd                    true
% 1.98/1.02  --prep_def_merge_tr_red                 false
% 1.98/1.02  --prep_def_merge_tr_cl                  false
% 1.98/1.02  --smt_preprocessing                     true
% 1.98/1.02  --smt_ac_axioms                         fast
% 1.98/1.02  --preprocessed_out                      false
% 1.98/1.02  --preprocessed_stats                    false
% 1.98/1.02  
% 1.98/1.02  ------ Abstraction refinement Options
% 1.98/1.02  
% 1.98/1.02  --abstr_ref                             []
% 1.98/1.02  --abstr_ref_prep                        false
% 1.98/1.02  --abstr_ref_until_sat                   false
% 1.98/1.02  --abstr_ref_sig_restrict                funpre
% 1.98/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.98/1.02  --abstr_ref_under                       []
% 1.98/1.02  
% 1.98/1.02  ------ SAT Options
% 1.98/1.02  
% 1.98/1.02  --sat_mode                              false
% 1.98/1.02  --sat_fm_restart_options                ""
% 1.98/1.02  --sat_gr_def                            false
% 1.98/1.02  --sat_epr_types                         true
% 1.98/1.02  --sat_non_cyclic_types                  false
% 1.98/1.02  --sat_finite_models                     false
% 1.98/1.02  --sat_fm_lemmas                         false
% 1.98/1.02  --sat_fm_prep                           false
% 1.98/1.02  --sat_fm_uc_incr                        true
% 1.98/1.02  --sat_out_model                         small
% 1.98/1.02  --sat_out_clauses                       false
% 1.98/1.02  
% 1.98/1.02  ------ QBF Options
% 1.98/1.02  
% 1.98/1.02  --qbf_mode                              false
% 1.98/1.02  --qbf_elim_univ                         false
% 1.98/1.02  --qbf_dom_inst                          none
% 1.98/1.02  --qbf_dom_pre_inst                      false
% 1.98/1.02  --qbf_sk_in                             false
% 1.98/1.02  --qbf_pred_elim                         true
% 1.98/1.02  --qbf_split                             512
% 1.98/1.02  
% 1.98/1.02  ------ BMC1 Options
% 1.98/1.02  
% 1.98/1.02  --bmc1_incremental                      false
% 1.98/1.02  --bmc1_axioms                           reachable_all
% 1.98/1.02  --bmc1_min_bound                        0
% 1.98/1.02  --bmc1_max_bound                        -1
% 1.98/1.02  --bmc1_max_bound_default                -1
% 1.98/1.02  --bmc1_symbol_reachability              true
% 1.98/1.02  --bmc1_property_lemmas                  false
% 1.98/1.02  --bmc1_k_induction                      false
% 1.98/1.02  --bmc1_non_equiv_states                 false
% 1.98/1.02  --bmc1_deadlock                         false
% 1.98/1.02  --bmc1_ucm                              false
% 1.98/1.02  --bmc1_add_unsat_core                   none
% 1.98/1.02  --bmc1_unsat_core_children              false
% 1.98/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.98/1.02  --bmc1_out_stat                         full
% 1.98/1.02  --bmc1_ground_init                      false
% 1.98/1.02  --bmc1_pre_inst_next_state              false
% 1.98/1.02  --bmc1_pre_inst_state                   false
% 1.98/1.02  --bmc1_pre_inst_reach_state             false
% 1.98/1.02  --bmc1_out_unsat_core                   false
% 1.98/1.02  --bmc1_aig_witness_out                  false
% 1.98/1.02  --bmc1_verbose                          false
% 1.98/1.02  --bmc1_dump_clauses_tptp                false
% 1.98/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.98/1.02  --bmc1_dump_file                        -
% 1.98/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.98/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.98/1.02  --bmc1_ucm_extend_mode                  1
% 1.98/1.02  --bmc1_ucm_init_mode                    2
% 1.98/1.02  --bmc1_ucm_cone_mode                    none
% 1.98/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.98/1.02  --bmc1_ucm_relax_model                  4
% 1.98/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.98/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.98/1.02  --bmc1_ucm_layered_model                none
% 1.98/1.02  --bmc1_ucm_max_lemma_size               10
% 1.98/1.02  
% 1.98/1.02  ------ AIG Options
% 1.98/1.02  
% 1.98/1.02  --aig_mode                              false
% 1.98/1.02  
% 1.98/1.02  ------ Instantiation Options
% 1.98/1.02  
% 1.98/1.02  --instantiation_flag                    true
% 1.98/1.02  --inst_sos_flag                         false
% 1.98/1.02  --inst_sos_phase                        true
% 1.98/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.98/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.98/1.02  --inst_lit_sel_side                     none
% 1.98/1.02  --inst_solver_per_active                1400
% 1.98/1.02  --inst_solver_calls_frac                1.
% 1.98/1.02  --inst_passive_queue_type               priority_queues
% 1.98/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.98/1.03  --inst_passive_queues_freq              [25;2]
% 1.98/1.03  --inst_dismatching                      true
% 1.98/1.03  --inst_eager_unprocessed_to_passive     true
% 1.98/1.03  --inst_prop_sim_given                   true
% 1.98/1.03  --inst_prop_sim_new                     false
% 1.98/1.03  --inst_subs_new                         false
% 1.98/1.03  --inst_eq_res_simp                      false
% 1.98/1.03  --inst_subs_given                       false
% 1.98/1.03  --inst_orphan_elimination               true
% 1.98/1.03  --inst_learning_loop_flag               true
% 1.98/1.03  --inst_learning_start                   3000
% 1.98/1.03  --inst_learning_factor                  2
% 1.98/1.03  --inst_start_prop_sim_after_learn       3
% 1.98/1.03  --inst_sel_renew                        solver
% 1.98/1.03  --inst_lit_activity_flag                true
% 1.98/1.03  --inst_restr_to_given                   false
% 1.98/1.03  --inst_activity_threshold               500
% 1.98/1.03  --inst_out_proof                        true
% 1.98/1.03  
% 1.98/1.03  ------ Resolution Options
% 1.98/1.03  
% 1.98/1.03  --resolution_flag                       false
% 1.98/1.03  --res_lit_sel                           adaptive
% 1.98/1.03  --res_lit_sel_side                      none
% 1.98/1.03  --res_ordering                          kbo
% 1.98/1.03  --res_to_prop_solver                    active
% 1.98/1.03  --res_prop_simpl_new                    false
% 1.98/1.03  --res_prop_simpl_given                  true
% 1.98/1.03  --res_passive_queue_type                priority_queues
% 1.98/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.98/1.03  --res_passive_queues_freq               [15;5]
% 1.98/1.03  --res_forward_subs                      full
% 1.98/1.03  --res_backward_subs                     full
% 1.98/1.03  --res_forward_subs_resolution           true
% 1.98/1.03  --res_backward_subs_resolution          true
% 1.98/1.03  --res_orphan_elimination                true
% 1.98/1.03  --res_time_limit                        2.
% 1.98/1.03  --res_out_proof                         true
% 1.98/1.03  
% 1.98/1.03  ------ Superposition Options
% 1.98/1.03  
% 1.98/1.03  --superposition_flag                    true
% 1.98/1.03  --sup_passive_queue_type                priority_queues
% 1.98/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.98/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.98/1.03  --demod_completeness_check              fast
% 1.98/1.03  --demod_use_ground                      true
% 1.98/1.03  --sup_to_prop_solver                    passive
% 1.98/1.03  --sup_prop_simpl_new                    true
% 1.98/1.03  --sup_prop_simpl_given                  true
% 1.98/1.03  --sup_fun_splitting                     false
% 1.98/1.03  --sup_smt_interval                      50000
% 1.98/1.03  
% 1.98/1.03  ------ Superposition Simplification Setup
% 1.98/1.03  
% 1.98/1.03  --sup_indices_passive                   []
% 1.98/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.98/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/1.03  --sup_full_bw                           [BwDemod]
% 1.98/1.03  --sup_immed_triv                        [TrivRules]
% 1.98/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.98/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/1.03  --sup_immed_bw_main                     []
% 1.98/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.98/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/1.03  
% 1.98/1.03  ------ Combination Options
% 1.98/1.03  
% 1.98/1.03  --comb_res_mult                         3
% 1.98/1.03  --comb_sup_mult                         2
% 1.98/1.03  --comb_inst_mult                        10
% 1.98/1.03  
% 1.98/1.03  ------ Debug Options
% 1.98/1.03  
% 1.98/1.03  --dbg_backtrace                         false
% 1.98/1.03  --dbg_dump_prop_clauses                 false
% 1.98/1.03  --dbg_dump_prop_clauses_file            -
% 1.98/1.03  --dbg_out_stat                          false
% 1.98/1.03  
% 1.98/1.03  
% 1.98/1.03  
% 1.98/1.03  
% 1.98/1.03  ------ Proving...
% 1.98/1.03  
% 1.98/1.03  
% 1.98/1.03  % SZS status Theorem for theBenchmark.p
% 1.98/1.03  
% 1.98/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.98/1.03  
% 1.98/1.03  fof(f7,axiom,(
% 1.98/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f58,plain,(
% 1.98/1.03    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.98/1.03    inference(cnf_transformation,[],[f7])).
% 1.98/1.03  
% 1.98/1.03  fof(f6,axiom,(
% 1.98/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f22,plain,(
% 1.98/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.98/1.03    inference(ennf_transformation,[],[f6])).
% 1.98/1.03  
% 1.98/1.03  fof(f38,plain,(
% 1.98/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.98/1.03    inference(nnf_transformation,[],[f22])).
% 1.98/1.03  
% 1.98/1.03  fof(f56,plain,(
% 1.98/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.98/1.03    inference(cnf_transformation,[],[f38])).
% 1.98/1.03  
% 1.98/1.03  fof(f14,axiom,(
% 1.98/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f20,plain,(
% 1.98/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.98/1.03    inference(pure_predicate_removal,[],[f14])).
% 1.98/1.03  
% 1.98/1.03  fof(f29,plain,(
% 1.98/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.98/1.03    inference(ennf_transformation,[],[f20])).
% 1.98/1.03  
% 1.98/1.03  fof(f68,plain,(
% 1.98/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.98/1.03    inference(cnf_transformation,[],[f29])).
% 1.98/1.03  
% 1.98/1.03  fof(f18,conjecture,(
% 1.98/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f19,negated_conjecture,(
% 1.98/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 1.98/1.03    inference(negated_conjecture,[],[f18])).
% 1.98/1.03  
% 1.98/1.03  fof(f34,plain,(
% 1.98/1.03    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.98/1.03    inference(ennf_transformation,[],[f19])).
% 1.98/1.03  
% 1.98/1.03  fof(f35,plain,(
% 1.98/1.03    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.98/1.03    inference(flattening,[],[f34])).
% 1.98/1.03  
% 1.98/1.03  fof(f41,plain,(
% 1.98/1.03    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 1.98/1.03    introduced(choice_axiom,[])).
% 1.98/1.03  
% 1.98/1.03  fof(f42,plain,(
% 1.98/1.03    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 1.98/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f41])).
% 1.98/1.03  
% 1.98/1.03  fof(f76,plain,(
% 1.98/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.98/1.03    inference(cnf_transformation,[],[f42])).
% 1.98/1.03  
% 1.98/1.03  fof(f2,axiom,(
% 1.98/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f44,plain,(
% 1.98/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.98/1.03    inference(cnf_transformation,[],[f2])).
% 1.98/1.03  
% 1.98/1.03  fof(f3,axiom,(
% 1.98/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f45,plain,(
% 1.98/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.98/1.03    inference(cnf_transformation,[],[f3])).
% 1.98/1.03  
% 1.98/1.03  fof(f4,axiom,(
% 1.98/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f46,plain,(
% 1.98/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.98/1.03    inference(cnf_transformation,[],[f4])).
% 1.98/1.03  
% 1.98/1.03  fof(f79,plain,(
% 1.98/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.98/1.03    inference(definition_unfolding,[],[f45,f46])).
% 1.98/1.03  
% 1.98/1.03  fof(f80,plain,(
% 1.98/1.03    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.98/1.03    inference(definition_unfolding,[],[f44,f79])).
% 1.98/1.03  
% 1.98/1.03  fof(f92,plain,(
% 1.98/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 1.98/1.03    inference(definition_unfolding,[],[f76,f80])).
% 1.98/1.03  
% 1.98/1.03  fof(f13,axiom,(
% 1.98/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f28,plain,(
% 1.98/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.98/1.03    inference(ennf_transformation,[],[f13])).
% 1.98/1.03  
% 1.98/1.03  fof(f67,plain,(
% 1.98/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.98/1.03    inference(cnf_transformation,[],[f28])).
% 1.98/1.03  
% 1.98/1.03  fof(f5,axiom,(
% 1.98/1.03    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f21,plain,(
% 1.98/1.03    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 1.98/1.03    inference(ennf_transformation,[],[f5])).
% 1.98/1.03  
% 1.98/1.03  fof(f36,plain,(
% 1.98/1.03    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.98/1.03    inference(nnf_transformation,[],[f21])).
% 1.98/1.03  
% 1.98/1.03  fof(f37,plain,(
% 1.98/1.03    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 1.98/1.03    inference(flattening,[],[f36])).
% 1.98/1.03  
% 1.98/1.03  fof(f47,plain,(
% 1.98/1.03    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 1.98/1.03    inference(cnf_transformation,[],[f37])).
% 1.98/1.03  
% 1.98/1.03  fof(f89,plain,(
% 1.98/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 1.98/1.03    inference(definition_unfolding,[],[f47,f46,f79,f79,f79,f80,f80,f80,f46])).
% 1.98/1.03  
% 1.98/1.03  fof(f16,axiom,(
% 1.98/1.03    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f31,plain,(
% 1.98/1.03    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.98/1.03    inference(ennf_transformation,[],[f16])).
% 1.98/1.03  
% 1.98/1.03  fof(f39,plain,(
% 1.98/1.03    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 1.98/1.03    introduced(choice_axiom,[])).
% 1.98/1.03  
% 1.98/1.03  fof(f40,plain,(
% 1.98/1.03    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 1.98/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f39])).
% 1.98/1.03  
% 1.98/1.03  fof(f70,plain,(
% 1.98/1.03    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.98/1.03    inference(cnf_transformation,[],[f40])).
% 1.98/1.03  
% 1.98/1.03  fof(f17,axiom,(
% 1.98/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f32,plain,(
% 1.98/1.03    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.98/1.03    inference(ennf_transformation,[],[f17])).
% 1.98/1.03  
% 1.98/1.03  fof(f33,plain,(
% 1.98/1.03    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.98/1.03    inference(flattening,[],[f32])).
% 1.98/1.03  
% 1.98/1.03  fof(f73,plain,(
% 1.98/1.03    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.98/1.03    inference(cnf_transformation,[],[f33])).
% 1.98/1.03  
% 1.98/1.03  fof(f75,plain,(
% 1.98/1.03    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 1.98/1.03    inference(cnf_transformation,[],[f42])).
% 1.98/1.03  
% 1.98/1.03  fof(f93,plain,(
% 1.98/1.03    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 1.98/1.03    inference(definition_unfolding,[],[f75,f80])).
% 1.98/1.03  
% 1.98/1.03  fof(f74,plain,(
% 1.98/1.03    v1_funct_1(sK3)),
% 1.98/1.03    inference(cnf_transformation,[],[f42])).
% 1.98/1.03  
% 1.98/1.03  fof(f77,plain,(
% 1.98/1.03    k1_xboole_0 != sK2),
% 1.98/1.03    inference(cnf_transformation,[],[f42])).
% 1.98/1.03  
% 1.98/1.03  fof(f15,axiom,(
% 1.98/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f30,plain,(
% 1.98/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.98/1.03    inference(ennf_transformation,[],[f15])).
% 1.98/1.03  
% 1.98/1.03  fof(f69,plain,(
% 1.98/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.98/1.03    inference(cnf_transformation,[],[f30])).
% 1.98/1.03  
% 1.98/1.03  fof(f12,axiom,(
% 1.98/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f27,plain,(
% 1.98/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.98/1.03    inference(ennf_transformation,[],[f12])).
% 1.98/1.03  
% 1.98/1.03  fof(f66,plain,(
% 1.98/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.98/1.03    inference(cnf_transformation,[],[f27])).
% 1.98/1.03  
% 1.98/1.03  fof(f78,plain,(
% 1.98/1.03    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)),
% 1.98/1.03    inference(cnf_transformation,[],[f42])).
% 1.98/1.03  
% 1.98/1.03  fof(f91,plain,(
% 1.98/1.03    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)),
% 1.98/1.03    inference(definition_unfolding,[],[f78,f80,f80])).
% 1.98/1.03  
% 1.98/1.03  fof(f11,axiom,(
% 1.98/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f25,plain,(
% 1.98/1.03    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.98/1.03    inference(ennf_transformation,[],[f11])).
% 1.98/1.03  
% 1.98/1.03  fof(f26,plain,(
% 1.98/1.03    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.98/1.03    inference(flattening,[],[f25])).
% 1.98/1.03  
% 1.98/1.03  fof(f65,plain,(
% 1.98/1.03    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.98/1.03    inference(cnf_transformation,[],[f26])).
% 1.98/1.03  
% 1.98/1.03  fof(f90,plain,(
% 1.98/1.03    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.98/1.03    inference(definition_unfolding,[],[f65,f80,f80])).
% 1.98/1.03  
% 1.98/1.03  fof(f8,axiom,(
% 1.98/1.03    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f23,plain,(
% 1.98/1.03    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.98/1.03    inference(ennf_transformation,[],[f8])).
% 1.98/1.03  
% 1.98/1.03  fof(f24,plain,(
% 1.98/1.03    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.98/1.03    inference(flattening,[],[f23])).
% 1.98/1.03  
% 1.98/1.03  fof(f60,plain,(
% 1.98/1.03    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.98/1.03    inference(cnf_transformation,[],[f24])).
% 1.98/1.03  
% 1.98/1.03  fof(f59,plain,(
% 1.98/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.98/1.03    inference(cnf_transformation,[],[f7])).
% 1.98/1.03  
% 1.98/1.03  fof(f1,axiom,(
% 1.98/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f43,plain,(
% 1.98/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.98/1.03    inference(cnf_transformation,[],[f1])).
% 1.98/1.03  
% 1.98/1.03  fof(f9,axiom,(
% 1.98/1.03    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f62,plain,(
% 1.98/1.03    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.98/1.03    inference(cnf_transformation,[],[f9])).
% 1.98/1.03  
% 1.98/1.03  fof(f10,axiom,(
% 1.98/1.03    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/1.03  
% 1.98/1.03  fof(f64,plain,(
% 1.98/1.03    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.98/1.03    inference(cnf_transformation,[],[f10])).
% 1.98/1.03  
% 1.98/1.03  fof(f63,plain,(
% 1.98/1.03    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.98/1.03    inference(cnf_transformation,[],[f10])).
% 1.98/1.03  
% 1.98/1.03  cnf(c_13,plain,
% 1.98/1.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.98/1.03      inference(cnf_transformation,[],[f58]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_11,plain,
% 1.98/1.03      ( ~ v4_relat_1(X0,X1)
% 1.98/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 1.98/1.03      | ~ v1_relat_1(X0) ),
% 1.98/1.03      inference(cnf_transformation,[],[f56]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_22,plain,
% 1.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.98/1.03      | v4_relat_1(X0,X1) ),
% 1.98/1.03      inference(cnf_transformation,[],[f68]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_30,negated_conjecture,
% 1.98/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 1.98/1.03      inference(cnf_transformation,[],[f92]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_345,plain,
% 1.98/1.03      ( v4_relat_1(X0,X1)
% 1.98/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.98/1.03      | sK3 != X0 ),
% 1.98/1.03      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_346,plain,
% 1.98/1.03      ( v4_relat_1(sK3,X0)
% 1.98/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.98/1.03      inference(unflattening,[status(thm)],[c_345]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_412,plain,
% 1.98/1.03      ( r1_tarski(k1_relat_1(X0),X1)
% 1.98/1.03      | ~ v1_relat_1(X0)
% 1.98/1.03      | X2 != X1
% 1.98/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 1.98/1.03      | sK3 != X0 ),
% 1.98/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_346]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_413,plain,
% 1.98/1.03      ( r1_tarski(k1_relat_1(sK3),X0)
% 1.98/1.03      | ~ v1_relat_1(sK3)
% 1.98/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.98/1.03      inference(unflattening,[status(thm)],[c_412]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_21,plain,
% 1.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.98/1.03      | v1_relat_1(X0) ),
% 1.98/1.03      inference(cnf_transformation,[],[f67]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_357,plain,
% 1.98/1.03      ( v1_relat_1(X0)
% 1.98/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.98/1.03      | sK3 != X0 ),
% 1.98/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_358,plain,
% 1.98/1.03      ( v1_relat_1(sK3)
% 1.98/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.98/1.03      inference(unflattening,[status(thm)],[c_357]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_417,plain,
% 1.98/1.03      ( r1_tarski(k1_relat_1(sK3),X0)
% 1.98/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.98/1.03      inference(global_propositional_subsumption,
% 1.98/1.03                [status(thm)],
% 1.98/1.03                [c_413,c_358]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1907,plain,
% 1.98/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.98/1.03      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2205,plain,
% 1.98/1.03      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 1.98/1.03      inference(equality_resolution,[status(thm)],[c_1907]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_9,plain,
% 1.98/1.03      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 1.98/1.03      | k2_enumset1(X1,X1,X2,X3) = X0
% 1.98/1.03      | k2_enumset1(X1,X1,X1,X3) = X0
% 1.98/1.03      | k2_enumset1(X2,X2,X2,X3) = X0
% 1.98/1.03      | k2_enumset1(X1,X1,X1,X2) = X0
% 1.98/1.03      | k2_enumset1(X3,X3,X3,X3) = X0
% 1.98/1.03      | k2_enumset1(X2,X2,X2,X2) = X0
% 1.98/1.03      | k2_enumset1(X1,X1,X1,X1) = X0
% 1.98/1.03      | k1_xboole_0 = X0 ),
% 1.98/1.03      inference(cnf_transformation,[],[f89]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1920,plain,
% 1.98/1.03      ( k2_enumset1(X0,X0,X1,X2) = X3
% 1.98/1.03      | k2_enumset1(X0,X0,X0,X2) = X3
% 1.98/1.03      | k2_enumset1(X1,X1,X1,X2) = X3
% 1.98/1.03      | k2_enumset1(X0,X0,X0,X1) = X3
% 1.98/1.03      | k2_enumset1(X2,X2,X2,X2) = X3
% 1.98/1.03      | k2_enumset1(X1,X1,X1,X1) = X3
% 1.98/1.03      | k2_enumset1(X0,X0,X0,X0) = X3
% 1.98/1.03      | k1_xboole_0 = X3
% 1.98/1.03      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2993,plain,
% 1.98/1.03      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 1.98/1.03      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.98/1.03      inference(superposition,[status(thm)],[c_2205,c_1920]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_26,plain,
% 1.98/1.03      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.98/1.03      inference(cnf_transformation,[],[f70]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1911,plain,
% 1.98/1.03      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_27,plain,
% 1.98/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 1.98/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.98/1.03      | ~ r2_hidden(X3,X1)
% 1.98/1.03      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 1.98/1.03      | ~ v1_funct_1(X0)
% 1.98/1.03      | k1_xboole_0 = X2 ),
% 1.98/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_31,negated_conjecture,
% 1.98/1.03      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 1.98/1.03      inference(cnf_transformation,[],[f93]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_315,plain,
% 1.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.98/1.03      | ~ r2_hidden(X3,X1)
% 1.98/1.03      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 1.98/1.03      | ~ v1_funct_1(X0)
% 1.98/1.03      | k2_enumset1(sK1,sK1,sK1,sK1) != X1
% 1.98/1.03      | sK2 != X2
% 1.98/1.03      | sK3 != X0
% 1.98/1.03      | k1_xboole_0 = X2 ),
% 1.98/1.03      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_316,plain,
% 1.98/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 1.98/1.03      | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 1.98/1.03      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3))
% 1.98/1.03      | ~ v1_funct_1(sK3)
% 1.98/1.03      | k1_xboole_0 = sK2 ),
% 1.98/1.03      inference(unflattening,[status(thm)],[c_315]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_32,negated_conjecture,
% 1.98/1.03      ( v1_funct_1(sK3) ),
% 1.98/1.03      inference(cnf_transformation,[],[f74]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_29,negated_conjecture,
% 1.98/1.03      ( k1_xboole_0 != sK2 ),
% 1.98/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_320,plain,
% 1.98/1.03      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 1.98/1.03      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) ),
% 1.98/1.03      inference(global_propositional_subsumption,
% 1.98/1.03                [status(thm)],
% 1.98/1.03                [c_316,c_32,c_30,c_29]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1909,plain,
% 1.98/1.03      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 1.98/1.03      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) = iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_23,plain,
% 1.98/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.98/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.98/1.03      inference(cnf_transformation,[],[f69]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_336,plain,
% 1.98/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.98/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.98/1.03      | sK3 != X2 ),
% 1.98/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_337,plain,
% 1.98/1.03      ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
% 1.98/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.98/1.03      inference(unflattening,[status(thm)],[c_336]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2108,plain,
% 1.98/1.03      ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 1.98/1.03      inference(equality_resolution,[status(thm)],[c_337]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2150,plain,
% 1.98/1.03      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 1.98/1.03      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 1.98/1.03      inference(light_normalisation,[status(thm)],[c_1909,c_2108]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2516,plain,
% 1.98/1.03      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
% 1.98/1.03      | r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),k2_relat_1(sK3)) = iProver_top ),
% 1.98/1.03      inference(superposition,[status(thm)],[c_1911,c_2150]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_20,plain,
% 1.98/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 1.98/1.03      inference(cnf_transformation,[],[f66]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1914,plain,
% 1.98/1.03      ( r2_hidden(X0,X1) != iProver_top
% 1.98/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2761,plain,
% 1.98/1.03      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
% 1.98/1.03      | r1_tarski(k2_relat_1(sK3),k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1)))) != iProver_top ),
% 1.98/1.03      inference(superposition,[status(thm)],[c_2516,c_1914]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_3191,plain,
% 1.98/1.03      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
% 1.98/1.03      | k1_relat_1(sK3) = k1_xboole_0
% 1.98/1.03      | r1_tarski(k2_relat_1(sK3),k1_funct_1(sK3,sK0(k1_relat_1(sK3)))) != iProver_top ),
% 1.98/1.03      inference(superposition,[status(thm)],[c_2993,c_2761]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_33,plain,
% 1.98/1.03      ( v1_funct_1(sK3) = iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1495,plain,( X0 = X0 ),theory(equality) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2087,plain,
% 1.98/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_1495]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2090,plain,
% 1.98/1.03      ( v1_relat_1(sK3)
% 1.98/1.03      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_358]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2091,plain,
% 1.98/1.03      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 1.98/1.03      | v1_relat_1(sK3) = iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_2090]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_28,negated_conjecture,
% 1.98/1.03      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
% 1.98/1.03      inference(cnf_transformation,[],[f91]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2133,plain,
% 1.98/1.03      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
% 1.98/1.03      inference(demodulation,[status(thm)],[c_2108,c_28]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_19,plain,
% 1.98/1.03      ( ~ v1_funct_1(X0)
% 1.98/1.03      | ~ v1_relat_1(X0)
% 1.98/1.03      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 1.98/1.03      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 1.98/1.03      inference(cnf_transformation,[],[f90]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1915,plain,
% 1.98/1.03      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
% 1.98/1.03      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
% 1.98/1.03      | v1_funct_1(X1) != iProver_top
% 1.98/1.03      | v1_relat_1(X1) != iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_3185,plain,
% 1.98/1.03      ( k2_enumset1(k1_funct_1(X0,sK1),k1_funct_1(X0,sK1),k1_funct_1(X0,sK1),k1_funct_1(X0,sK1)) = k2_relat_1(X0)
% 1.98/1.03      | k1_relat_1(X0) != k1_relat_1(sK3)
% 1.98/1.03      | k1_relat_1(sK3) = k1_xboole_0
% 1.98/1.03      | v1_funct_1(X0) != iProver_top
% 1.98/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.98/1.03      inference(superposition,[status(thm)],[c_2993,c_1915]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_3767,plain,
% 1.98/1.03      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
% 1.98/1.03      | k1_relat_1(sK3) = k1_xboole_0
% 1.98/1.03      | v1_funct_1(sK3) != iProver_top
% 1.98/1.03      | v1_relat_1(sK3) != iProver_top ),
% 1.98/1.03      inference(equality_resolution,[status(thm)],[c_3185]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_3820,plain,
% 1.98/1.03      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 1.98/1.03      inference(global_propositional_subsumption,
% 1.98/1.03                [status(thm)],
% 1.98/1.03                [c_3191,c_33,c_2087,c_2091,c_2133,c_3767]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_15,plain,
% 1.98/1.03      ( ~ v1_relat_1(X0)
% 1.98/1.03      | k1_relat_1(X0) != k1_xboole_0
% 1.98/1.03      | k1_xboole_0 = X0 ),
% 1.98/1.03      inference(cnf_transformation,[],[f60]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1918,plain,
% 1.98/1.03      ( k1_relat_1(X0) != k1_xboole_0
% 1.98/1.03      | k1_xboole_0 = X0
% 1.98/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_3833,plain,
% 1.98/1.03      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 1.98/1.03      inference(superposition,[status(thm)],[c_3820,c_1918]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2176,plain,
% 1.98/1.03      ( ~ v1_relat_1(sK3)
% 1.98/1.03      | k1_relat_1(sK3) != k1_xboole_0
% 1.98/1.03      | k1_xboole_0 = sK3 ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_15]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2616,plain,
% 1.98/1.03      ( sK3 = sK3 ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_1495]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1496,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2429,plain,
% 1.98/1.03      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_1496]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2926,plain,
% 1.98/1.03      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_2429]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2928,plain,
% 1.98/1.03      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_2926]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_3836,plain,
% 1.98/1.03      ( sK3 = k1_xboole_0 ),
% 1.98/1.03      inference(global_propositional_subsumption,
% 1.98/1.03                [status(thm)],
% 1.98/1.03                [c_3833,c_33,c_2087,c_2090,c_2091,c_2133,c_2176,c_2616,
% 1.98/1.03                 c_2928,c_3767]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_3840,plain,
% 1.98/1.03      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
% 1.98/1.03      | r1_tarski(k2_relat_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK1,sK1,sK1,sK1)))) != iProver_top ),
% 1.98/1.03      inference(demodulation,[status(thm)],[c_3836,c_2761]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_12,plain,
% 1.98/1.03      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.98/1.03      inference(cnf_transformation,[],[f59]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_3871,plain,
% 1.98/1.03      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0
% 1.98/1.03      | r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,sK0(k2_enumset1(sK1,sK1,sK1,sK1)))) != iProver_top ),
% 1.98/1.03      inference(light_normalisation,[status(thm)],[c_3840,c_12]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_0,plain,
% 1.98/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 1.98/1.03      inference(cnf_transformation,[],[f43]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1929,plain,
% 1.98/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_4069,plain,
% 1.98/1.03      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0 ),
% 1.98/1.03      inference(forward_subsumption_resolution,
% 1.98/1.03                [status(thm)],
% 1.98/1.03                [c_3871,c_1929]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_4095,plain,
% 1.98/1.03      ( k2_enumset1(k1_funct_1(X0,sK1),k1_funct_1(X0,sK1),k1_funct_1(X0,sK1),k1_funct_1(X0,sK1)) = k2_relat_1(X0)
% 1.98/1.03      | k1_relat_1(X0) != k1_xboole_0
% 1.98/1.03      | v1_funct_1(X0) != iProver_top
% 1.98/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.98/1.03      inference(superposition,[status(thm)],[c_4069,c_1915]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_4254,plain,
% 1.98/1.03      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) = k2_relat_1(k1_xboole_0)
% 1.98/1.03      | v1_funct_1(k1_xboole_0) != iProver_top
% 1.98/1.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.98/1.03      inference(superposition,[status(thm)],[c_13,c_4095]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_4255,plain,
% 1.98/1.03      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) = k1_xboole_0
% 1.98/1.03      | v1_funct_1(k1_xboole_0) != iProver_top
% 1.98/1.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.98/1.03      inference(light_normalisation,[status(thm)],[c_4254,c_12]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_3844,plain,
% 1.98/1.03      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) != k2_relat_1(k1_xboole_0) ),
% 1.98/1.03      inference(demodulation,[status(thm)],[c_3836,c_2133]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_3857,plain,
% 1.98/1.03      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) != k1_xboole_0 ),
% 1.98/1.03      inference(light_normalisation,[status(thm)],[c_3844,c_12]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2245,plain,
% 1.98/1.03      ( X0 != X1 | X0 = k6_relat_1(X2) | k6_relat_1(X2) != X1 ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_1496]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2246,plain,
% 1.98/1.03      ( k6_relat_1(k1_xboole_0) != k1_xboole_0
% 1.98/1.03      | k1_xboole_0 = k6_relat_1(k1_xboole_0)
% 1.98/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_2245]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1500,plain,
% 1.98/1.03      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 1.98/1.03      theory(equality) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2127,plain,
% 1.98/1.03      ( v1_relat_1(X0)
% 1.98/1.03      | ~ v1_relat_1(k6_relat_1(X1))
% 1.98/1.03      | X0 != k6_relat_1(X1) ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_1500]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2128,plain,
% 1.98/1.03      ( X0 != k6_relat_1(X1)
% 1.98/1.03      | v1_relat_1(X0) = iProver_top
% 1.98/1.03      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_2127]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2130,plain,
% 1.98/1.03      ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
% 1.98/1.03      | v1_relat_1(k6_relat_1(k1_xboole_0)) != iProver_top
% 1.98/1.03      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_2128]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1503,plain,
% 1.98/1.03      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 1.98/1.03      theory(equality) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2109,plain,
% 1.98/1.03      ( v1_funct_1(X0)
% 1.98/1.03      | ~ v1_funct_1(k6_relat_1(X1))
% 1.98/1.03      | X0 != k6_relat_1(X1) ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_1503]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2110,plain,
% 1.98/1.03      ( X0 != k6_relat_1(X1)
% 1.98/1.03      | v1_funct_1(X0) = iProver_top
% 1.98/1.03      | v1_funct_1(k6_relat_1(X1)) != iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_2109]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_2112,plain,
% 1.98/1.03      ( k1_xboole_0 != k6_relat_1(k1_xboole_0)
% 1.98/1.03      | v1_funct_1(k6_relat_1(k1_xboole_0)) != iProver_top
% 1.98/1.03      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_2110]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_1522,plain,
% 1.98/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_1495]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_16,plain,
% 1.98/1.03      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.98/1.03      inference(cnf_transformation,[],[f62]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_17,plain,
% 1.98/1.03      ( v1_funct_1(k6_relat_1(X0)) ),
% 1.98/1.03      inference(cnf_transformation,[],[f64]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_64,plain,
% 1.98/1.03      ( v1_funct_1(k6_relat_1(X0)) = iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_66,plain,
% 1.98/1.03      ( v1_funct_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_64]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_18,plain,
% 1.98/1.03      ( v1_relat_1(k6_relat_1(X0)) ),
% 1.98/1.03      inference(cnf_transformation,[],[f63]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_61,plain,
% 1.98/1.03      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 1.98/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(c_63,plain,
% 1.98/1.03      ( v1_relat_1(k6_relat_1(k1_xboole_0)) = iProver_top ),
% 1.98/1.03      inference(instantiation,[status(thm)],[c_61]) ).
% 1.98/1.03  
% 1.98/1.03  cnf(contradiction,plain,
% 1.98/1.03      ( $false ),
% 1.98/1.03      inference(minisat,
% 1.98/1.03                [status(thm)],
% 1.98/1.03                [c_4255,c_3857,c_2246,c_2130,c_2112,c_1522,c_16,c_66,
% 1.98/1.03                 c_63]) ).
% 1.98/1.03  
% 1.98/1.03  
% 1.98/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.98/1.03  
% 1.98/1.03  ------                               Statistics
% 1.98/1.03  
% 1.98/1.03  ------ General
% 1.98/1.03  
% 1.98/1.03  abstr_ref_over_cycles:                  0
% 1.98/1.03  abstr_ref_under_cycles:                 0
% 1.98/1.03  gc_basic_clause_elim:                   0
% 1.98/1.03  forced_gc_time:                         0
% 1.98/1.03  parsing_time:                           0.007
% 1.98/1.03  unif_index_cands_time:                  0.
% 1.98/1.03  unif_index_add_time:                    0.
% 1.98/1.03  orderings_time:                         0.
% 1.98/1.03  out_proof_time:                         0.012
% 1.98/1.03  total_time:                             0.114
% 1.98/1.03  num_of_symbols:                         52
% 1.98/1.03  num_of_terms:                           3046
% 1.98/1.03  
% 1.98/1.03  ------ Preprocessing
% 1.98/1.03  
% 1.98/1.03  num_of_splits:                          0
% 1.98/1.03  num_of_split_atoms:                     0
% 1.98/1.03  num_of_reused_defs:                     0
% 1.98/1.03  num_eq_ax_congr_red:                    17
% 1.98/1.03  num_of_sem_filtered_clauses:            1
% 1.98/1.03  num_of_subtypes:                        0
% 1.98/1.03  monotx_restored_types:                  0
% 1.98/1.03  sat_num_of_epr_types:                   0
% 1.98/1.03  sat_num_of_non_cyclic_types:            0
% 1.98/1.03  sat_guarded_non_collapsed_types:        0
% 1.98/1.03  num_pure_diseq_elim:                    0
% 1.98/1.03  simp_replaced_by:                       0
% 1.98/1.03  res_preprocessed:                       149
% 1.98/1.03  prep_upred:                             0
% 1.98/1.03  prep_unflattend:                        88
% 1.98/1.03  smt_new_axioms:                         0
% 1.98/1.03  pred_elim_cands:                        4
% 1.98/1.03  pred_elim:                              3
% 1.98/1.03  pred_elim_cl:                           4
% 1.98/1.03  pred_elim_cycles:                       9
% 1.98/1.03  merged_defs:                            0
% 1.98/1.03  merged_defs_ncl:                        0
% 1.98/1.03  bin_hyper_res:                          0
% 1.98/1.03  prep_cycles:                            4
% 1.98/1.03  pred_elim_time:                         0.012
% 1.98/1.03  splitting_time:                         0.
% 1.98/1.03  sem_filter_time:                        0.
% 1.98/1.03  monotx_time:                            0.
% 1.98/1.03  subtype_inf_time:                       0.
% 1.98/1.03  
% 1.98/1.03  ------ Problem properties
% 1.98/1.03  
% 1.98/1.03  clauses:                                29
% 1.98/1.03  conjectures:                            3
% 1.98/1.03  epr:                                    4
% 1.98/1.03  horn:                                   27
% 1.98/1.03  ground:                                 6
% 1.98/1.03  unary:                                  17
% 1.98/1.03  binary:                                 6
% 1.98/1.03  lits:                                   54
% 1.98/1.03  lits_eq:                                28
% 1.98/1.03  fd_pure:                                0
% 1.98/1.03  fd_pseudo:                              0
% 1.98/1.03  fd_cond:                                5
% 1.98/1.03  fd_pseudo_cond:                         1
% 1.98/1.03  ac_symbols:                             0
% 1.98/1.03  
% 1.98/1.03  ------ Propositional Solver
% 1.98/1.03  
% 1.98/1.03  prop_solver_calls:                      28
% 1.98/1.03  prop_fast_solver_calls:                 986
% 1.98/1.03  smt_solver_calls:                       0
% 1.98/1.03  smt_fast_solver_calls:                  0
% 1.98/1.03  prop_num_of_clauses:                    1068
% 1.98/1.03  prop_preprocess_simplified:             5252
% 1.98/1.03  prop_fo_subsumed:                       18
% 1.98/1.03  prop_solver_time:                       0.
% 1.98/1.03  smt_solver_time:                        0.
% 1.98/1.03  smt_fast_solver_time:                   0.
% 1.98/1.03  prop_fast_solver_time:                  0.
% 1.98/1.03  prop_unsat_core_time:                   0.
% 1.98/1.03  
% 1.98/1.03  ------ QBF
% 1.98/1.03  
% 1.98/1.03  qbf_q_res:                              0
% 1.98/1.03  qbf_num_tautologies:                    0
% 1.98/1.03  qbf_prep_cycles:                        0
% 1.98/1.03  
% 1.98/1.03  ------ BMC1
% 1.98/1.03  
% 1.98/1.03  bmc1_current_bound:                     -1
% 1.98/1.03  bmc1_last_solved_bound:                 -1
% 1.98/1.03  bmc1_unsat_core_size:                   -1
% 1.98/1.03  bmc1_unsat_core_parents_size:           -1
% 1.98/1.03  bmc1_merge_next_fun:                    0
% 1.98/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.98/1.03  
% 1.98/1.03  ------ Instantiation
% 1.98/1.03  
% 1.98/1.03  inst_num_of_clauses:                    424
% 1.98/1.03  inst_num_in_passive:                    105
% 1.98/1.03  inst_num_in_active:                     255
% 1.98/1.03  inst_num_in_unprocessed:                64
% 1.98/1.03  inst_num_of_loops:                      310
% 1.98/1.03  inst_num_of_learning_restarts:          0
% 1.98/1.03  inst_num_moves_active_passive:          52
% 1.98/1.03  inst_lit_activity:                      0
% 1.98/1.03  inst_lit_activity_moves:                0
% 1.98/1.03  inst_num_tautologies:                   0
% 1.98/1.03  inst_num_prop_implied:                  0
% 1.98/1.03  inst_num_existing_simplified:           0
% 1.98/1.03  inst_num_eq_res_simplified:             0
% 1.98/1.03  inst_num_child_elim:                    0
% 1.98/1.03  inst_num_of_dismatching_blockings:      47
% 1.98/1.03  inst_num_of_non_proper_insts:           327
% 1.98/1.03  inst_num_of_duplicates:                 0
% 1.98/1.03  inst_inst_num_from_inst_to_res:         0
% 1.98/1.03  inst_dismatching_checking_time:         0.
% 1.98/1.03  
% 1.98/1.03  ------ Resolution
% 1.98/1.03  
% 1.98/1.03  res_num_of_clauses:                     0
% 1.98/1.03  res_num_in_passive:                     0
% 1.98/1.03  res_num_in_active:                      0
% 1.98/1.03  res_num_of_loops:                       153
% 1.98/1.03  res_forward_subset_subsumed:            52
% 1.98/1.03  res_backward_subset_subsumed:           2
% 1.98/1.03  res_forward_subsumed:                   2
% 1.98/1.03  res_backward_subsumed:                  0
% 1.98/1.03  res_forward_subsumption_resolution:     0
% 1.98/1.03  res_backward_subsumption_resolution:    0
% 1.98/1.03  res_clause_to_clause_subsumption:       244
% 1.98/1.03  res_orphan_elimination:                 0
% 1.98/1.03  res_tautology_del:                      72
% 1.98/1.03  res_num_eq_res_simplified:              0
% 1.98/1.03  res_num_sel_changes:                    0
% 1.98/1.03  res_moves_from_active_to_pass:          0
% 1.98/1.03  
% 1.98/1.03  ------ Superposition
% 1.98/1.03  
% 1.98/1.03  sup_time_total:                         0.
% 1.98/1.03  sup_time_generating:                    0.
% 1.98/1.03  sup_time_sim_full:                      0.
% 1.98/1.03  sup_time_sim_immed:                     0.
% 1.98/1.03  
% 1.98/1.03  sup_num_of_clauses:                     35
% 1.98/1.03  sup_num_in_active:                      32
% 1.98/1.03  sup_num_in_passive:                     3
% 1.98/1.03  sup_num_of_loops:                       61
% 1.98/1.03  sup_fw_superposition:                   23
% 1.98/1.03  sup_bw_superposition:                   50
% 1.98/1.03  sup_immediate_simplified:               25
% 1.98/1.03  sup_given_eliminated:                   0
% 1.98/1.03  comparisons_done:                       0
% 1.98/1.03  comparisons_avoided:                    6
% 1.98/1.03  
% 1.98/1.03  ------ Simplifications
% 1.98/1.03  
% 1.98/1.03  
% 1.98/1.03  sim_fw_subset_subsumed:                 5
% 1.98/1.03  sim_bw_subset_subsumed:                 8
% 1.98/1.03  sim_fw_subsumed:                        12
% 1.98/1.03  sim_bw_subsumed:                        0
% 1.98/1.03  sim_fw_subsumption_res:                 1
% 1.98/1.03  sim_bw_subsumption_res:                 0
% 1.98/1.03  sim_tautology_del:                      0
% 1.98/1.03  sim_eq_tautology_del:                   18
% 1.98/1.03  sim_eq_res_simp:                        0
% 1.98/1.03  sim_fw_demodulated:                     1
% 1.98/1.03  sim_bw_demodulated:                     22
% 1.98/1.03  sim_light_normalised:                   9
% 1.98/1.03  sim_joinable_taut:                      0
% 1.98/1.03  sim_joinable_simp:                      0
% 1.98/1.03  sim_ac_normalised:                      0
% 1.98/1.03  sim_smt_subsumption:                    0
% 1.98/1.03  
%------------------------------------------------------------------------------
