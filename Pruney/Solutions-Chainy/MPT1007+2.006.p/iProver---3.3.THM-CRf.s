%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:43 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 364 expanded)
%              Number of clauses        :   55 (  85 expanded)
%              Number of leaves         :   17 (  81 expanded)
%              Depth                    :   17
%              Number of atoms          :  454 (1324 expanded)
%              Number of equality atoms :  209 ( 528 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,
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

fof(f46,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f45])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f82])).

fof(f92,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f79,f83])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f44,plain,(
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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f78,f83])).

fof(f80,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f50,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f90,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f59])).

fof(f98,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f90])).

fof(f99,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f98])).

fof(f81,plain,(
    ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1417,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_16,plain,
    ( ~ v5_relat_1(X0,X1)
    | m1_subset_1(k1_funct_1(X0,X2),X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_16])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_341,plain,
    ( ~ r2_hidden(X3,k1_relat_1(X0))
    | m1_subset_1(k1_funct_1(X0,X3),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_337,c_17])).

cnf(c_342,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_341])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_342,c_31])).

cnf(c_501,plain,
    ( m1_subset_1(k1_funct_1(sK4,X0),X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r2_hidden(X0,k1_relat_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_1414,plain,
    ( m1_subset_1(k1_funct_1(sK4,X0),X1) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_1689,plain,
    ( m1_subset_1(k1_funct_1(sK4,X0),sK3) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1417,c_1414])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1422,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2873,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1689,c_1422])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1432,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_515,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_516,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
    | ~ v1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_1413,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_517,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_1625,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1626,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1625])).

cnf(c_1665,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1413,c_34,c_517,c_1626])).

cnf(c_1666,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_1665])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1431,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2166,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1666,c_1431])).

cnf(c_2367,plain,
    ( v1_xboole_0(k1_relat_1(sK4)) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1432,c_2166])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1420,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3007,plain,
    ( v1_xboole_0(sK3) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1417,c_1420])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1419,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2867,plain,
    ( k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1417,c_1419])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_733,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_enumset1(sK2,sK2,sK2,sK2)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_732])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_735,plain,
    ( k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_733,c_29,c_28])).

cnf(c_3181,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_2867,c_735])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1424,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3633,plain,
    ( r2_hidden(sK2,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3181,c_1424])).

cnf(c_3818,plain,
    ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3633,c_1431])).

cnf(c_4644,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2873,c_2367,c_3007,c_3818])).

cnf(c_4645,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4644])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1418,plain,
    ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4654,plain,
    ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4645,c_1418])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4654,c_3633])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.65/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.01  
% 2.65/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.65/1.01  
% 2.65/1.01  ------  iProver source info
% 2.65/1.01  
% 2.65/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.65/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.65/1.01  git: non_committed_changes: false
% 2.65/1.01  git: last_make_outside_of_git: false
% 2.65/1.01  
% 2.65/1.01  ------ 
% 2.65/1.01  
% 2.65/1.01  ------ Input Options
% 2.65/1.01  
% 2.65/1.01  --out_options                           all
% 2.65/1.01  --tptp_safe_out                         true
% 2.65/1.01  --problem_path                          ""
% 2.65/1.01  --include_path                          ""
% 2.65/1.01  --clausifier                            res/vclausify_rel
% 2.65/1.01  --clausifier_options                    --mode clausify
% 2.65/1.01  --stdin                                 false
% 2.65/1.01  --stats_out                             all
% 2.65/1.01  
% 2.65/1.01  ------ General Options
% 2.65/1.01  
% 2.65/1.01  --fof                                   false
% 2.65/1.01  --time_out_real                         305.
% 2.65/1.01  --time_out_virtual                      -1.
% 2.65/1.01  --symbol_type_check                     false
% 2.65/1.01  --clausify_out                          false
% 2.65/1.01  --sig_cnt_out                           false
% 2.65/1.01  --trig_cnt_out                          false
% 2.65/1.01  --trig_cnt_out_tolerance                1.
% 2.65/1.01  --trig_cnt_out_sk_spl                   false
% 2.65/1.01  --abstr_cl_out                          false
% 2.65/1.01  
% 2.65/1.01  ------ Global Options
% 2.65/1.01  
% 2.65/1.01  --schedule                              default
% 2.65/1.01  --add_important_lit                     false
% 2.65/1.01  --prop_solver_per_cl                    1000
% 2.65/1.01  --min_unsat_core                        false
% 2.65/1.01  --soft_assumptions                      false
% 2.65/1.01  --soft_lemma_size                       3
% 2.65/1.01  --prop_impl_unit_size                   0
% 2.65/1.01  --prop_impl_unit                        []
% 2.65/1.01  --share_sel_clauses                     true
% 2.65/1.01  --reset_solvers                         false
% 2.65/1.01  --bc_imp_inh                            [conj_cone]
% 2.65/1.01  --conj_cone_tolerance                   3.
% 2.65/1.01  --extra_neg_conj                        none
% 2.65/1.01  --large_theory_mode                     true
% 2.65/1.01  --prolific_symb_bound                   200
% 2.65/1.01  --lt_threshold                          2000
% 2.65/1.01  --clause_weak_htbl                      true
% 2.65/1.01  --gc_record_bc_elim                     false
% 2.65/1.01  
% 2.65/1.01  ------ Preprocessing Options
% 2.65/1.01  
% 2.65/1.01  --preprocessing_flag                    true
% 2.65/1.01  --time_out_prep_mult                    0.1
% 2.65/1.01  --splitting_mode                        input
% 2.65/1.01  --splitting_grd                         true
% 2.65/1.01  --splitting_cvd                         false
% 2.65/1.01  --splitting_cvd_svl                     false
% 2.65/1.01  --splitting_nvd                         32
% 2.65/1.01  --sub_typing                            true
% 2.65/1.01  --prep_gs_sim                           true
% 2.65/1.01  --prep_unflatten                        true
% 2.65/1.01  --prep_res_sim                          true
% 2.65/1.01  --prep_upred                            true
% 2.65/1.01  --prep_sem_filter                       exhaustive
% 2.65/1.01  --prep_sem_filter_out                   false
% 2.65/1.01  --pred_elim                             true
% 2.65/1.01  --res_sim_input                         true
% 2.65/1.01  --eq_ax_congr_red                       true
% 2.65/1.01  --pure_diseq_elim                       true
% 2.65/1.01  --brand_transform                       false
% 2.65/1.01  --non_eq_to_eq                          false
% 2.65/1.01  --prep_def_merge                        true
% 2.65/1.01  --prep_def_merge_prop_impl              false
% 2.65/1.01  --prep_def_merge_mbd                    true
% 2.65/1.01  --prep_def_merge_tr_red                 false
% 2.65/1.01  --prep_def_merge_tr_cl                  false
% 2.65/1.01  --smt_preprocessing                     true
% 2.65/1.01  --smt_ac_axioms                         fast
% 2.65/1.01  --preprocessed_out                      false
% 2.65/1.01  --preprocessed_stats                    false
% 2.65/1.01  
% 2.65/1.01  ------ Abstraction refinement Options
% 2.65/1.01  
% 2.65/1.01  --abstr_ref                             []
% 2.65/1.01  --abstr_ref_prep                        false
% 2.65/1.01  --abstr_ref_until_sat                   false
% 2.65/1.01  --abstr_ref_sig_restrict                funpre
% 2.65/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/1.01  --abstr_ref_under                       []
% 2.65/1.01  
% 2.65/1.01  ------ SAT Options
% 2.65/1.01  
% 2.65/1.01  --sat_mode                              false
% 2.65/1.01  --sat_fm_restart_options                ""
% 2.65/1.01  --sat_gr_def                            false
% 2.65/1.01  --sat_epr_types                         true
% 2.65/1.01  --sat_non_cyclic_types                  false
% 2.65/1.01  --sat_finite_models                     false
% 2.65/1.01  --sat_fm_lemmas                         false
% 2.65/1.01  --sat_fm_prep                           false
% 2.65/1.01  --sat_fm_uc_incr                        true
% 2.65/1.01  --sat_out_model                         small
% 2.65/1.01  --sat_out_clauses                       false
% 2.65/1.01  
% 2.65/1.01  ------ QBF Options
% 2.65/1.01  
% 2.65/1.01  --qbf_mode                              false
% 2.65/1.01  --qbf_elim_univ                         false
% 2.65/1.01  --qbf_dom_inst                          none
% 2.65/1.01  --qbf_dom_pre_inst                      false
% 2.65/1.01  --qbf_sk_in                             false
% 2.65/1.01  --qbf_pred_elim                         true
% 2.65/1.01  --qbf_split                             512
% 2.65/1.01  
% 2.65/1.01  ------ BMC1 Options
% 2.65/1.01  
% 2.65/1.01  --bmc1_incremental                      false
% 2.65/1.01  --bmc1_axioms                           reachable_all
% 2.65/1.01  --bmc1_min_bound                        0
% 2.65/1.01  --bmc1_max_bound                        -1
% 2.65/1.01  --bmc1_max_bound_default                -1
% 2.65/1.01  --bmc1_symbol_reachability              true
% 2.65/1.01  --bmc1_property_lemmas                  false
% 2.65/1.01  --bmc1_k_induction                      false
% 2.65/1.01  --bmc1_non_equiv_states                 false
% 2.65/1.01  --bmc1_deadlock                         false
% 2.65/1.01  --bmc1_ucm                              false
% 2.65/1.01  --bmc1_add_unsat_core                   none
% 2.65/1.01  --bmc1_unsat_core_children              false
% 2.65/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/1.01  --bmc1_out_stat                         full
% 2.65/1.01  --bmc1_ground_init                      false
% 2.65/1.01  --bmc1_pre_inst_next_state              false
% 2.65/1.01  --bmc1_pre_inst_state                   false
% 2.65/1.01  --bmc1_pre_inst_reach_state             false
% 2.65/1.01  --bmc1_out_unsat_core                   false
% 2.65/1.01  --bmc1_aig_witness_out                  false
% 2.65/1.01  --bmc1_verbose                          false
% 2.65/1.01  --bmc1_dump_clauses_tptp                false
% 2.65/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.65/1.01  --bmc1_dump_file                        -
% 2.65/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.65/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.65/1.01  --bmc1_ucm_extend_mode                  1
% 2.65/1.01  --bmc1_ucm_init_mode                    2
% 2.65/1.01  --bmc1_ucm_cone_mode                    none
% 2.65/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.65/1.01  --bmc1_ucm_relax_model                  4
% 2.65/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.65/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/1.01  --bmc1_ucm_layered_model                none
% 2.65/1.01  --bmc1_ucm_max_lemma_size               10
% 2.65/1.01  
% 2.65/1.01  ------ AIG Options
% 2.65/1.01  
% 2.65/1.01  --aig_mode                              false
% 2.65/1.01  
% 2.65/1.01  ------ Instantiation Options
% 2.65/1.01  
% 2.65/1.01  --instantiation_flag                    true
% 2.65/1.01  --inst_sos_flag                         false
% 2.65/1.01  --inst_sos_phase                        true
% 2.65/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/1.01  --inst_lit_sel_side                     num_symb
% 2.65/1.01  --inst_solver_per_active                1400
% 2.65/1.01  --inst_solver_calls_frac                1.
% 2.65/1.01  --inst_passive_queue_type               priority_queues
% 2.65/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/1.01  --inst_passive_queues_freq              [25;2]
% 2.65/1.01  --inst_dismatching                      true
% 2.65/1.01  --inst_eager_unprocessed_to_passive     true
% 2.65/1.01  --inst_prop_sim_given                   true
% 2.65/1.01  --inst_prop_sim_new                     false
% 2.65/1.01  --inst_subs_new                         false
% 2.65/1.01  --inst_eq_res_simp                      false
% 2.65/1.01  --inst_subs_given                       false
% 2.65/1.01  --inst_orphan_elimination               true
% 2.65/1.01  --inst_learning_loop_flag               true
% 2.65/1.01  --inst_learning_start                   3000
% 2.65/1.01  --inst_learning_factor                  2
% 2.65/1.01  --inst_start_prop_sim_after_learn       3
% 2.65/1.01  --inst_sel_renew                        solver
% 2.65/1.01  --inst_lit_activity_flag                true
% 2.65/1.01  --inst_restr_to_given                   false
% 2.65/1.01  --inst_activity_threshold               500
% 2.65/1.01  --inst_out_proof                        true
% 2.65/1.01  
% 2.65/1.01  ------ Resolution Options
% 2.65/1.01  
% 2.65/1.01  --resolution_flag                       true
% 2.65/1.01  --res_lit_sel                           adaptive
% 2.65/1.01  --res_lit_sel_side                      none
% 2.65/1.01  --res_ordering                          kbo
% 2.65/1.01  --res_to_prop_solver                    active
% 2.65/1.01  --res_prop_simpl_new                    false
% 2.65/1.01  --res_prop_simpl_given                  true
% 2.65/1.01  --res_passive_queue_type                priority_queues
% 2.65/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/1.01  --res_passive_queues_freq               [15;5]
% 2.65/1.01  --res_forward_subs                      full
% 2.65/1.01  --res_backward_subs                     full
% 2.65/1.01  --res_forward_subs_resolution           true
% 2.65/1.01  --res_backward_subs_resolution          true
% 2.65/1.01  --res_orphan_elimination                true
% 2.65/1.01  --res_time_limit                        2.
% 2.65/1.01  --res_out_proof                         true
% 2.65/1.01  
% 2.65/1.01  ------ Superposition Options
% 2.65/1.01  
% 2.65/1.01  --superposition_flag                    true
% 2.65/1.01  --sup_passive_queue_type                priority_queues
% 2.65/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.65/1.01  --demod_completeness_check              fast
% 2.65/1.01  --demod_use_ground                      true
% 2.65/1.01  --sup_to_prop_solver                    passive
% 2.65/1.01  --sup_prop_simpl_new                    true
% 2.65/1.01  --sup_prop_simpl_given                  true
% 2.65/1.01  --sup_fun_splitting                     false
% 2.65/1.01  --sup_smt_interval                      50000
% 2.65/1.01  
% 2.65/1.01  ------ Superposition Simplification Setup
% 2.65/1.01  
% 2.65/1.01  --sup_indices_passive                   []
% 2.65/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.01  --sup_full_bw                           [BwDemod]
% 2.65/1.01  --sup_immed_triv                        [TrivRules]
% 2.65/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.01  --sup_immed_bw_main                     []
% 2.65/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/1.01  
% 2.65/1.01  ------ Combination Options
% 2.65/1.01  
% 2.65/1.01  --comb_res_mult                         3
% 2.65/1.01  --comb_sup_mult                         2
% 2.65/1.01  --comb_inst_mult                        10
% 2.65/1.01  
% 2.65/1.01  ------ Debug Options
% 2.65/1.01  
% 2.65/1.01  --dbg_backtrace                         false
% 2.65/1.01  --dbg_dump_prop_clauses                 false
% 2.65/1.01  --dbg_dump_prop_clauses_file            -
% 2.65/1.01  --dbg_out_stat                          false
% 2.65/1.01  ------ Parsing...
% 2.65/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.65/1.01  
% 2.65/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.65/1.01  
% 2.65/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.65/1.01  
% 2.65/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.65/1.01  ------ Proving...
% 2.65/1.01  ------ Problem Properties 
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  clauses                                 27
% 2.65/1.01  conjectures                             3
% 2.65/1.01  EPR                                     3
% 2.65/1.01  Horn                                    21
% 2.65/1.01  unary                                   7
% 2.65/1.01  binary                                  4
% 2.65/1.01  lits                                    68
% 2.65/1.01  lits eq                                 24
% 2.65/1.01  fd_pure                                 0
% 2.65/1.01  fd_pseudo                               0
% 2.65/1.01  fd_cond                                 0
% 2.65/1.01  fd_pseudo_cond                          5
% 2.65/1.01  AC symbols                              0
% 2.65/1.01  
% 2.65/1.01  ------ Schedule dynamic 5 is on 
% 2.65/1.01  
% 2.65/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  ------ 
% 2.65/1.01  Current options:
% 2.65/1.01  ------ 
% 2.65/1.01  
% 2.65/1.01  ------ Input Options
% 2.65/1.01  
% 2.65/1.01  --out_options                           all
% 2.65/1.01  --tptp_safe_out                         true
% 2.65/1.01  --problem_path                          ""
% 2.65/1.01  --include_path                          ""
% 2.65/1.01  --clausifier                            res/vclausify_rel
% 2.65/1.01  --clausifier_options                    --mode clausify
% 2.65/1.01  --stdin                                 false
% 2.65/1.01  --stats_out                             all
% 2.65/1.01  
% 2.65/1.01  ------ General Options
% 2.65/1.01  
% 2.65/1.01  --fof                                   false
% 2.65/1.01  --time_out_real                         305.
% 2.65/1.01  --time_out_virtual                      -1.
% 2.65/1.01  --symbol_type_check                     false
% 2.65/1.01  --clausify_out                          false
% 2.65/1.01  --sig_cnt_out                           false
% 2.65/1.01  --trig_cnt_out                          false
% 2.65/1.01  --trig_cnt_out_tolerance                1.
% 2.65/1.01  --trig_cnt_out_sk_spl                   false
% 2.65/1.01  --abstr_cl_out                          false
% 2.65/1.01  
% 2.65/1.01  ------ Global Options
% 2.65/1.01  
% 2.65/1.01  --schedule                              default
% 2.65/1.01  --add_important_lit                     false
% 2.65/1.01  --prop_solver_per_cl                    1000
% 2.65/1.01  --min_unsat_core                        false
% 2.65/1.01  --soft_assumptions                      false
% 2.65/1.01  --soft_lemma_size                       3
% 2.65/1.01  --prop_impl_unit_size                   0
% 2.65/1.01  --prop_impl_unit                        []
% 2.65/1.01  --share_sel_clauses                     true
% 2.65/1.01  --reset_solvers                         false
% 2.65/1.01  --bc_imp_inh                            [conj_cone]
% 2.65/1.01  --conj_cone_tolerance                   3.
% 2.65/1.01  --extra_neg_conj                        none
% 2.65/1.01  --large_theory_mode                     true
% 2.65/1.01  --prolific_symb_bound                   200
% 2.65/1.01  --lt_threshold                          2000
% 2.65/1.01  --clause_weak_htbl                      true
% 2.65/1.01  --gc_record_bc_elim                     false
% 2.65/1.01  
% 2.65/1.01  ------ Preprocessing Options
% 2.65/1.01  
% 2.65/1.01  --preprocessing_flag                    true
% 2.65/1.01  --time_out_prep_mult                    0.1
% 2.65/1.01  --splitting_mode                        input
% 2.65/1.01  --splitting_grd                         true
% 2.65/1.01  --splitting_cvd                         false
% 2.65/1.01  --splitting_cvd_svl                     false
% 2.65/1.01  --splitting_nvd                         32
% 2.65/1.01  --sub_typing                            true
% 2.65/1.01  --prep_gs_sim                           true
% 2.65/1.01  --prep_unflatten                        true
% 2.65/1.01  --prep_res_sim                          true
% 2.65/1.01  --prep_upred                            true
% 2.65/1.01  --prep_sem_filter                       exhaustive
% 2.65/1.01  --prep_sem_filter_out                   false
% 2.65/1.01  --pred_elim                             true
% 2.65/1.01  --res_sim_input                         true
% 2.65/1.01  --eq_ax_congr_red                       true
% 2.65/1.01  --pure_diseq_elim                       true
% 2.65/1.01  --brand_transform                       false
% 2.65/1.01  --non_eq_to_eq                          false
% 2.65/1.01  --prep_def_merge                        true
% 2.65/1.01  --prep_def_merge_prop_impl              false
% 2.65/1.01  --prep_def_merge_mbd                    true
% 2.65/1.01  --prep_def_merge_tr_red                 false
% 2.65/1.01  --prep_def_merge_tr_cl                  false
% 2.65/1.01  --smt_preprocessing                     true
% 2.65/1.01  --smt_ac_axioms                         fast
% 2.65/1.01  --preprocessed_out                      false
% 2.65/1.01  --preprocessed_stats                    false
% 2.65/1.01  
% 2.65/1.01  ------ Abstraction refinement Options
% 2.65/1.01  
% 2.65/1.01  --abstr_ref                             []
% 2.65/1.01  --abstr_ref_prep                        false
% 2.65/1.01  --abstr_ref_until_sat                   false
% 2.65/1.01  --abstr_ref_sig_restrict                funpre
% 2.65/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/1.01  --abstr_ref_under                       []
% 2.65/1.01  
% 2.65/1.01  ------ SAT Options
% 2.65/1.01  
% 2.65/1.01  --sat_mode                              false
% 2.65/1.01  --sat_fm_restart_options                ""
% 2.65/1.01  --sat_gr_def                            false
% 2.65/1.01  --sat_epr_types                         true
% 2.65/1.01  --sat_non_cyclic_types                  false
% 2.65/1.01  --sat_finite_models                     false
% 2.65/1.01  --sat_fm_lemmas                         false
% 2.65/1.01  --sat_fm_prep                           false
% 2.65/1.01  --sat_fm_uc_incr                        true
% 2.65/1.01  --sat_out_model                         small
% 2.65/1.01  --sat_out_clauses                       false
% 2.65/1.01  
% 2.65/1.01  ------ QBF Options
% 2.65/1.01  
% 2.65/1.01  --qbf_mode                              false
% 2.65/1.01  --qbf_elim_univ                         false
% 2.65/1.01  --qbf_dom_inst                          none
% 2.65/1.01  --qbf_dom_pre_inst                      false
% 2.65/1.01  --qbf_sk_in                             false
% 2.65/1.01  --qbf_pred_elim                         true
% 2.65/1.01  --qbf_split                             512
% 2.65/1.01  
% 2.65/1.01  ------ BMC1 Options
% 2.65/1.01  
% 2.65/1.01  --bmc1_incremental                      false
% 2.65/1.01  --bmc1_axioms                           reachable_all
% 2.65/1.01  --bmc1_min_bound                        0
% 2.65/1.01  --bmc1_max_bound                        -1
% 2.65/1.01  --bmc1_max_bound_default                -1
% 2.65/1.01  --bmc1_symbol_reachability              true
% 2.65/1.01  --bmc1_property_lemmas                  false
% 2.65/1.01  --bmc1_k_induction                      false
% 2.65/1.01  --bmc1_non_equiv_states                 false
% 2.65/1.01  --bmc1_deadlock                         false
% 2.65/1.01  --bmc1_ucm                              false
% 2.65/1.01  --bmc1_add_unsat_core                   none
% 2.65/1.01  --bmc1_unsat_core_children              false
% 2.65/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/1.01  --bmc1_out_stat                         full
% 2.65/1.01  --bmc1_ground_init                      false
% 2.65/1.01  --bmc1_pre_inst_next_state              false
% 2.65/1.01  --bmc1_pre_inst_state                   false
% 2.65/1.01  --bmc1_pre_inst_reach_state             false
% 2.65/1.01  --bmc1_out_unsat_core                   false
% 2.65/1.01  --bmc1_aig_witness_out                  false
% 2.65/1.01  --bmc1_verbose                          false
% 2.65/1.01  --bmc1_dump_clauses_tptp                false
% 2.65/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.65/1.01  --bmc1_dump_file                        -
% 2.65/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.65/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.65/1.01  --bmc1_ucm_extend_mode                  1
% 2.65/1.01  --bmc1_ucm_init_mode                    2
% 2.65/1.01  --bmc1_ucm_cone_mode                    none
% 2.65/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.65/1.01  --bmc1_ucm_relax_model                  4
% 2.65/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.65/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/1.01  --bmc1_ucm_layered_model                none
% 2.65/1.01  --bmc1_ucm_max_lemma_size               10
% 2.65/1.01  
% 2.65/1.01  ------ AIG Options
% 2.65/1.01  
% 2.65/1.01  --aig_mode                              false
% 2.65/1.01  
% 2.65/1.01  ------ Instantiation Options
% 2.65/1.01  
% 2.65/1.01  --instantiation_flag                    true
% 2.65/1.01  --inst_sos_flag                         false
% 2.65/1.01  --inst_sos_phase                        true
% 2.65/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/1.01  --inst_lit_sel_side                     none
% 2.65/1.01  --inst_solver_per_active                1400
% 2.65/1.01  --inst_solver_calls_frac                1.
% 2.65/1.01  --inst_passive_queue_type               priority_queues
% 2.65/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/1.01  --inst_passive_queues_freq              [25;2]
% 2.65/1.01  --inst_dismatching                      true
% 2.65/1.01  --inst_eager_unprocessed_to_passive     true
% 2.65/1.01  --inst_prop_sim_given                   true
% 2.65/1.01  --inst_prop_sim_new                     false
% 2.65/1.01  --inst_subs_new                         false
% 2.65/1.01  --inst_eq_res_simp                      false
% 2.65/1.01  --inst_subs_given                       false
% 2.65/1.01  --inst_orphan_elimination               true
% 2.65/1.01  --inst_learning_loop_flag               true
% 2.65/1.01  --inst_learning_start                   3000
% 2.65/1.01  --inst_learning_factor                  2
% 2.65/1.01  --inst_start_prop_sim_after_learn       3
% 2.65/1.01  --inst_sel_renew                        solver
% 2.65/1.01  --inst_lit_activity_flag                true
% 2.65/1.01  --inst_restr_to_given                   false
% 2.65/1.01  --inst_activity_threshold               500
% 2.65/1.01  --inst_out_proof                        true
% 2.65/1.01  
% 2.65/1.01  ------ Resolution Options
% 2.65/1.01  
% 2.65/1.01  --resolution_flag                       false
% 2.65/1.01  --res_lit_sel                           adaptive
% 2.65/1.01  --res_lit_sel_side                      none
% 2.65/1.01  --res_ordering                          kbo
% 2.65/1.01  --res_to_prop_solver                    active
% 2.65/1.01  --res_prop_simpl_new                    false
% 2.65/1.01  --res_prop_simpl_given                  true
% 2.65/1.01  --res_passive_queue_type                priority_queues
% 2.65/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/1.01  --res_passive_queues_freq               [15;5]
% 2.65/1.01  --res_forward_subs                      full
% 2.65/1.01  --res_backward_subs                     full
% 2.65/1.01  --res_forward_subs_resolution           true
% 2.65/1.01  --res_backward_subs_resolution          true
% 2.65/1.01  --res_orphan_elimination                true
% 2.65/1.01  --res_time_limit                        2.
% 2.65/1.01  --res_out_proof                         true
% 2.65/1.01  
% 2.65/1.01  ------ Superposition Options
% 2.65/1.01  
% 2.65/1.01  --superposition_flag                    true
% 2.65/1.01  --sup_passive_queue_type                priority_queues
% 2.65/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.65/1.01  --demod_completeness_check              fast
% 2.65/1.01  --demod_use_ground                      true
% 2.65/1.01  --sup_to_prop_solver                    passive
% 2.65/1.01  --sup_prop_simpl_new                    true
% 2.65/1.01  --sup_prop_simpl_given                  true
% 2.65/1.01  --sup_fun_splitting                     false
% 2.65/1.01  --sup_smt_interval                      50000
% 2.65/1.01  
% 2.65/1.01  ------ Superposition Simplification Setup
% 2.65/1.01  
% 2.65/1.01  --sup_indices_passive                   []
% 2.65/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.01  --sup_full_bw                           [BwDemod]
% 2.65/1.01  --sup_immed_triv                        [TrivRules]
% 2.65/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.01  --sup_immed_bw_main                     []
% 2.65/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/1.01  
% 2.65/1.01  ------ Combination Options
% 2.65/1.01  
% 2.65/1.01  --comb_res_mult                         3
% 2.65/1.01  --comb_sup_mult                         2
% 2.65/1.01  --comb_inst_mult                        10
% 2.65/1.01  
% 2.65/1.01  ------ Debug Options
% 2.65/1.01  
% 2.65/1.01  --dbg_backtrace                         false
% 2.65/1.01  --dbg_dump_prop_clauses                 false
% 2.65/1.01  --dbg_dump_prop_clauses_file            -
% 2.65/1.01  --dbg_out_stat                          false
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  ------ Proving...
% 2.65/1.01  
% 2.65/1.01  
% 2.65/1.01  % SZS status Theorem for theBenchmark.p
% 2.65/1.01  
% 2.65/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.65/1.01  
% 2.65/1.01  fof(f15,conjecture,(
% 2.65/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f16,negated_conjecture,(
% 2.65/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.65/1.01    inference(negated_conjecture,[],[f15])).
% 2.65/1.01  
% 2.65/1.01  fof(f32,plain,(
% 2.65/1.01    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.65/1.01    inference(ennf_transformation,[],[f16])).
% 2.65/1.01  
% 2.65/1.01  fof(f33,plain,(
% 2.65/1.01    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.65/1.01    inference(flattening,[],[f32])).
% 2.65/1.01  
% 2.65/1.01  fof(f45,plain,(
% 2.65/1.01    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 2.65/1.01    introduced(choice_axiom,[])).
% 2.65/1.01  
% 2.65/1.01  fof(f46,plain,(
% 2.65/1.01    ~r2_hidden(k1_funct_1(sK4,sK2),sK3) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 2.65/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f45])).
% 2.65/1.01  
% 2.65/1.01  fof(f79,plain,(
% 2.65/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 2.65/1.01    inference(cnf_transformation,[],[f46])).
% 2.65/1.01  
% 2.65/1.01  fof(f3,axiom,(
% 2.65/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f57,plain,(
% 2.65/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f3])).
% 2.65/1.01  
% 2.65/1.01  fof(f4,axiom,(
% 2.65/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f58,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f4])).
% 2.65/1.01  
% 2.65/1.01  fof(f5,axiom,(
% 2.65/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f59,plain,(
% 2.65/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f5])).
% 2.65/1.01  
% 2.65/1.01  fof(f82,plain,(
% 2.65/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.65/1.01    inference(definition_unfolding,[],[f58,f59])).
% 2.65/1.01  
% 2.65/1.01  fof(f83,plain,(
% 2.65/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.65/1.01    inference(definition_unfolding,[],[f57,f82])).
% 2.65/1.01  
% 2.65/1.01  fof(f92,plain,(
% 2.65/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))),
% 2.65/1.01    inference(definition_unfolding,[],[f79,f83])).
% 2.65/1.01  
% 2.65/1.01  fof(f11,axiom,(
% 2.65/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f17,plain,(
% 2.65/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.65/1.01    inference(pure_predicate_removal,[],[f11])).
% 2.65/1.01  
% 2.65/1.01  fof(f27,plain,(
% 2.65/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/1.01    inference(ennf_transformation,[],[f17])).
% 2.65/1.01  
% 2.65/1.01  fof(f68,plain,(
% 2.65/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/1.01    inference(cnf_transformation,[],[f27])).
% 2.65/1.01  
% 2.65/1.01  fof(f9,axiom,(
% 2.65/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 2.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f24,plain,(
% 2.65/1.01    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 2.65/1.01    inference(ennf_transformation,[],[f9])).
% 2.65/1.01  
% 2.65/1.01  fof(f25,plain,(
% 2.65/1.01    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 2.65/1.01    inference(flattening,[],[f24])).
% 2.65/1.01  
% 2.65/1.01  fof(f66,plain,(
% 2.65/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f25])).
% 2.65/1.01  
% 2.65/1.01  fof(f10,axiom,(
% 2.65/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f26,plain,(
% 2.65/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/1.01    inference(ennf_transformation,[],[f10])).
% 2.65/1.01  
% 2.65/1.01  fof(f67,plain,(
% 2.65/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/1.01    inference(cnf_transformation,[],[f26])).
% 2.65/1.01  
% 2.65/1.01  fof(f77,plain,(
% 2.65/1.01    v1_funct_1(sK4)),
% 2.65/1.01    inference(cnf_transformation,[],[f46])).
% 2.65/1.01  
% 2.65/1.01  fof(f6,axiom,(
% 2.65/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f19,plain,(
% 2.65/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.65/1.01    inference(ennf_transformation,[],[f6])).
% 2.65/1.01  
% 2.65/1.01  fof(f20,plain,(
% 2.65/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.65/1.01    inference(flattening,[],[f19])).
% 2.65/1.01  
% 2.65/1.01  fof(f60,plain,(
% 2.65/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f20])).
% 2.65/1.01  
% 2.65/1.01  fof(f1,axiom,(
% 2.65/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f34,plain,(
% 2.65/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.65/1.01    inference(nnf_transformation,[],[f1])).
% 2.65/1.01  
% 2.65/1.01  fof(f35,plain,(
% 2.65/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.65/1.01    inference(rectify,[],[f34])).
% 2.65/1.01  
% 2.65/1.01  fof(f36,plain,(
% 2.65/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.65/1.01    introduced(choice_axiom,[])).
% 2.65/1.01  
% 2.65/1.01  fof(f37,plain,(
% 2.65/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.65/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 2.65/1.01  
% 2.65/1.01  fof(f48,plain,(
% 2.65/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.65/1.01    inference(cnf_transformation,[],[f37])).
% 2.65/1.01  
% 2.65/1.01  fof(f8,axiom,(
% 2.65/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 2.65/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.01  
% 2.65/1.01  fof(f22,plain,(
% 2.65/1.01    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.65/1.01    inference(ennf_transformation,[],[f8])).
% 2.65/1.02  
% 2.65/1.02  fof(f23,plain,(
% 2.65/1.02    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/1.02    inference(flattening,[],[f22])).
% 2.65/1.02  
% 2.65/1.02  fof(f43,plain,(
% 2.65/1.02    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/1.02    inference(nnf_transformation,[],[f23])).
% 2.65/1.02  
% 2.65/1.02  fof(f62,plain,(
% 2.65/1.02    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/1.02    inference(cnf_transformation,[],[f43])).
% 2.65/1.02  
% 2.65/1.02  fof(f103,plain,(
% 2.65/1.02    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/1.02    inference(equality_resolution,[],[f62])).
% 2.65/1.02  
% 2.65/1.02  fof(f47,plain,(
% 2.65/1.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.65/1.02    inference(cnf_transformation,[],[f37])).
% 2.65/1.02  
% 2.65/1.02  fof(f12,axiom,(
% 2.65/1.02    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.02  
% 2.65/1.02  fof(f28,plain,(
% 2.65/1.02    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.65/1.02    inference(ennf_transformation,[],[f12])).
% 2.65/1.02  
% 2.65/1.02  fof(f69,plain,(
% 2.65/1.02    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 2.65/1.02    inference(cnf_transformation,[],[f28])).
% 2.65/1.02  
% 2.65/1.02  fof(f13,axiom,(
% 2.65/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.02  
% 2.65/1.02  fof(f29,plain,(
% 2.65/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/1.02    inference(ennf_transformation,[],[f13])).
% 2.65/1.02  
% 2.65/1.02  fof(f70,plain,(
% 2.65/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/1.02    inference(cnf_transformation,[],[f29])).
% 2.65/1.02  
% 2.65/1.02  fof(f14,axiom,(
% 2.65/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.02  
% 2.65/1.02  fof(f30,plain,(
% 2.65/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/1.02    inference(ennf_transformation,[],[f14])).
% 2.65/1.02  
% 2.65/1.02  fof(f31,plain,(
% 2.65/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/1.02    inference(flattening,[],[f30])).
% 2.65/1.02  
% 2.65/1.02  fof(f44,plain,(
% 2.65/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/1.02    inference(nnf_transformation,[],[f31])).
% 2.65/1.02  
% 2.65/1.02  fof(f71,plain,(
% 2.65/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/1.02    inference(cnf_transformation,[],[f44])).
% 2.65/1.02  
% 2.65/1.02  fof(f78,plain,(
% 2.65/1.02    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 2.65/1.02    inference(cnf_transformation,[],[f46])).
% 2.65/1.02  
% 2.65/1.02  fof(f93,plain,(
% 2.65/1.02    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 2.65/1.02    inference(definition_unfolding,[],[f78,f83])).
% 2.65/1.02  
% 2.65/1.02  fof(f80,plain,(
% 2.65/1.02    k1_xboole_0 != sK3),
% 2.65/1.02    inference(cnf_transformation,[],[f46])).
% 2.65/1.02  
% 2.65/1.02  fof(f2,axiom,(
% 2.65/1.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.65/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/1.02  
% 2.65/1.02  fof(f18,plain,(
% 2.65/1.02    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.65/1.02    inference(ennf_transformation,[],[f2])).
% 2.65/1.02  
% 2.65/1.02  fof(f38,plain,(
% 2.65/1.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.65/1.02    inference(nnf_transformation,[],[f18])).
% 2.65/1.02  
% 2.65/1.02  fof(f39,plain,(
% 2.65/1.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.65/1.02    inference(flattening,[],[f38])).
% 2.65/1.02  
% 2.65/1.02  fof(f40,plain,(
% 2.65/1.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.65/1.02    inference(rectify,[],[f39])).
% 2.65/1.02  
% 2.65/1.02  fof(f41,plain,(
% 2.65/1.02    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 2.65/1.02    introduced(choice_axiom,[])).
% 2.65/1.02  
% 2.65/1.02  fof(f42,plain,(
% 2.65/1.02    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.65/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 2.65/1.02  
% 2.65/1.02  fof(f50,plain,(
% 2.65/1.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.65/1.02    inference(cnf_transformation,[],[f42])).
% 2.65/1.02  
% 2.65/1.02  fof(f90,plain,(
% 2.65/1.02    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 2.65/1.02    inference(definition_unfolding,[],[f50,f59])).
% 2.65/1.02  
% 2.65/1.02  fof(f98,plain,(
% 2.65/1.02    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 2.65/1.02    inference(equality_resolution,[],[f90])).
% 2.65/1.02  
% 2.65/1.02  fof(f99,plain,(
% 2.65/1.02    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 2.65/1.02    inference(equality_resolution,[],[f98])).
% 2.65/1.02  
% 2.65/1.02  fof(f81,plain,(
% 2.65/1.02    ~r2_hidden(k1_funct_1(sK4,sK2),sK3)),
% 2.65/1.02    inference(cnf_transformation,[],[f46])).
% 2.65/1.02  
% 2.65/1.02  cnf(c_29,negated_conjecture,
% 2.65/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
% 2.65/1.02      inference(cnf_transformation,[],[f92]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1417,plain,
% 2.65/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_18,plain,
% 2.65/1.02      ( v5_relat_1(X0,X1)
% 2.65/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.65/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_16,plain,
% 2.65/1.02      ( ~ v5_relat_1(X0,X1)
% 2.65/1.02      | m1_subset_1(k1_funct_1(X0,X2),X1)
% 2.65/1.02      | ~ r2_hidden(X2,k1_relat_1(X0))
% 2.65/1.02      | ~ v1_relat_1(X0)
% 2.65/1.02      | ~ v1_funct_1(X0) ),
% 2.65/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_337,plain,
% 2.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/1.02      | m1_subset_1(k1_funct_1(X0,X3),X2)
% 2.65/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.65/1.02      | ~ v1_relat_1(X0)
% 2.65/1.02      | ~ v1_funct_1(X0) ),
% 2.65/1.02      inference(resolution,[status(thm)],[c_18,c_16]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_17,plain,
% 2.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/1.02      | v1_relat_1(X0) ),
% 2.65/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_341,plain,
% 2.65/1.02      ( ~ r2_hidden(X3,k1_relat_1(X0))
% 2.65/1.02      | m1_subset_1(k1_funct_1(X0,X3),X2)
% 2.65/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/1.02      | ~ v1_funct_1(X0) ),
% 2.65/1.02      inference(global_propositional_subsumption,
% 2.65/1.02                [status(thm)],
% 2.65/1.02                [c_337,c_17]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_342,plain,
% 2.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/1.02      | m1_subset_1(k1_funct_1(X0,X3),X2)
% 2.65/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.65/1.02      | ~ v1_funct_1(X0) ),
% 2.65/1.02      inference(renaming,[status(thm)],[c_341]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_31,negated_conjecture,
% 2.65/1.02      ( v1_funct_1(sK4) ),
% 2.65/1.02      inference(cnf_transformation,[],[f77]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_500,plain,
% 2.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/1.02      | m1_subset_1(k1_funct_1(X0,X3),X2)
% 2.65/1.02      | ~ r2_hidden(X3,k1_relat_1(X0))
% 2.65/1.02      | sK4 != X0 ),
% 2.65/1.02      inference(resolution_lifted,[status(thm)],[c_342,c_31]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_501,plain,
% 2.65/1.02      ( m1_subset_1(k1_funct_1(sK4,X0),X1)
% 2.65/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.65/1.02      | ~ r2_hidden(X0,k1_relat_1(sK4)) ),
% 2.65/1.02      inference(unflattening,[status(thm)],[c_500]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1414,plain,
% 2.65/1.02      ( m1_subset_1(k1_funct_1(sK4,X0),X1) = iProver_top
% 2.65/1.02      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.65/1.02      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1689,plain,
% 2.65/1.02      ( m1_subset_1(k1_funct_1(sK4,X0),sK3) = iProver_top
% 2.65/1.02      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.65/1.02      inference(superposition,[status(thm)],[c_1417,c_1414]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_10,plain,
% 2.65/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.65/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1422,plain,
% 2.65/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 2.65/1.02      | r2_hidden(X0,X1) = iProver_top
% 2.65/1.02      | v1_xboole_0(X1) = iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_2873,plain,
% 2.65/1.02      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.65/1.02      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top
% 2.65/1.02      | v1_xboole_0(sK3) = iProver_top ),
% 2.65/1.02      inference(superposition,[status(thm)],[c_1689,c_1422]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_0,plain,
% 2.65/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.65/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1432,plain,
% 2.65/1.02      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.65/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_15,plain,
% 2.65/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.65/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.65/1.02      | ~ v1_relat_1(X1)
% 2.65/1.02      | ~ v1_funct_1(X1) ),
% 2.65/1.02      inference(cnf_transformation,[],[f103]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_515,plain,
% 2.65/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.65/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 2.65/1.02      | ~ v1_relat_1(X1)
% 2.65/1.02      | sK4 != X1 ),
% 2.65/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_516,plain,
% 2.65/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.65/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4)
% 2.65/1.02      | ~ v1_relat_1(sK4) ),
% 2.65/1.02      inference(unflattening,[status(thm)],[c_515]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1413,plain,
% 2.65/1.02      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.65/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
% 2.65/1.02      | v1_relat_1(sK4) != iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_34,plain,
% 2.65/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_517,plain,
% 2.65/1.02      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.65/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
% 2.65/1.02      | v1_relat_1(sK4) != iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1625,plain,
% 2.65/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 2.65/1.02      | v1_relat_1(sK4) ),
% 2.65/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1626,plain,
% 2.65/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top
% 2.65/1.02      | v1_relat_1(sK4) = iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_1625]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1665,plain,
% 2.65/1.02      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top
% 2.65/1.02      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.65/1.02      inference(global_propositional_subsumption,
% 2.65/1.02                [status(thm)],
% 2.65/1.02                [c_1413,c_34,c_517,c_1626]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1666,plain,
% 2.65/1.02      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.65/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK4,X0)),sK4) = iProver_top ),
% 2.65/1.02      inference(renaming,[status(thm)],[c_1665]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1,plain,
% 2.65/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.65/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1431,plain,
% 2.65/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.65/1.02      | v1_xboole_0(X1) != iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_2166,plain,
% 2.65/1.02      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.65/1.02      | v1_xboole_0(sK4) != iProver_top ),
% 2.65/1.02      inference(superposition,[status(thm)],[c_1666,c_1431]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_2367,plain,
% 2.65/1.02      ( v1_xboole_0(k1_relat_1(sK4)) = iProver_top
% 2.65/1.02      | v1_xboole_0(sK4) != iProver_top ),
% 2.65/1.02      inference(superposition,[status(thm)],[c_1432,c_2166]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_19,plain,
% 2.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/1.02      | ~ v1_xboole_0(X2)
% 2.65/1.02      | v1_xboole_0(X0) ),
% 2.65/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1420,plain,
% 2.65/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.65/1.02      | v1_xboole_0(X2) != iProver_top
% 2.65/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_3007,plain,
% 2.65/1.02      ( v1_xboole_0(sK3) != iProver_top
% 2.65/1.02      | v1_xboole_0(sK4) = iProver_top ),
% 2.65/1.02      inference(superposition,[status(thm)],[c_1417,c_1420]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_20,plain,
% 2.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.65/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1419,plain,
% 2.65/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.65/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_2867,plain,
% 2.65/1.02      ( k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
% 2.65/1.02      inference(superposition,[status(thm)],[c_1417,c_1419]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_26,plain,
% 2.65/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.65/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.65/1.02      | k1_xboole_0 = X2 ),
% 2.65/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_30,negated_conjecture,
% 2.65/1.02      ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 2.65/1.02      inference(cnf_transformation,[],[f93]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_732,plain,
% 2.65/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/1.02      | k2_enumset1(sK2,sK2,sK2,sK2) != X1
% 2.65/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.65/1.02      | sK3 != X2
% 2.65/1.02      | sK4 != X0
% 2.65/1.02      | k1_xboole_0 = X2 ),
% 2.65/1.02      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_733,plain,
% 2.65/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 2.65/1.02      | k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_enumset1(sK2,sK2,sK2,sK2)
% 2.65/1.02      | k1_xboole_0 = sK3 ),
% 2.65/1.02      inference(unflattening,[status(thm)],[c_732]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_28,negated_conjecture,
% 2.65/1.02      ( k1_xboole_0 != sK3 ),
% 2.65/1.02      inference(cnf_transformation,[],[f80]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_735,plain,
% 2.65/1.02      ( k1_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 2.65/1.02      inference(global_propositional_subsumption,
% 2.65/1.02                [status(thm)],
% 2.65/1.02                [c_733,c_29,c_28]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_3181,plain,
% 2.65/1.02      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
% 2.65/1.02      inference(demodulation,[status(thm)],[c_2867,c_735]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_8,plain,
% 2.65/1.02      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 2.65/1.02      inference(cnf_transformation,[],[f99]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1424,plain,
% 2.65/1.02      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_3633,plain,
% 2.65/1.02      ( r2_hidden(sK2,k1_relat_1(sK4)) = iProver_top ),
% 2.65/1.02      inference(superposition,[status(thm)],[c_3181,c_1424]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_3818,plain,
% 2.65/1.02      ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top ),
% 2.65/1.02      inference(superposition,[status(thm)],[c_3633,c_1431]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_4644,plain,
% 2.65/1.02      ( r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top
% 2.65/1.02      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.65/1.02      inference(global_propositional_subsumption,
% 2.65/1.02                [status(thm)],
% 2.65/1.02                [c_2873,c_2367,c_3007,c_3818]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_4645,plain,
% 2.65/1.02      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.65/1.02      | r2_hidden(k1_funct_1(sK4,X0),sK3) = iProver_top ),
% 2.65/1.02      inference(renaming,[status(thm)],[c_4644]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_27,negated_conjecture,
% 2.65/1.02      ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
% 2.65/1.02      inference(cnf_transformation,[],[f81]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_1418,plain,
% 2.65/1.02      ( r2_hidden(k1_funct_1(sK4,sK2),sK3) != iProver_top ),
% 2.65/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(c_4654,plain,
% 2.65/1.02      ( r2_hidden(sK2,k1_relat_1(sK4)) != iProver_top ),
% 2.65/1.02      inference(superposition,[status(thm)],[c_4645,c_1418]) ).
% 2.65/1.02  
% 2.65/1.02  cnf(contradiction,plain,
% 2.65/1.02      ( $false ),
% 2.65/1.02      inference(minisat,[status(thm)],[c_4654,c_3633]) ).
% 2.65/1.02  
% 2.65/1.02  
% 2.65/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.65/1.02  
% 2.65/1.02  ------                               Statistics
% 2.65/1.02  
% 2.65/1.02  ------ General
% 2.65/1.02  
% 2.65/1.02  abstr_ref_over_cycles:                  0
% 2.65/1.02  abstr_ref_under_cycles:                 0
% 2.65/1.02  gc_basic_clause_elim:                   0
% 2.65/1.02  forced_gc_time:                         0
% 2.65/1.02  parsing_time:                           0.007
% 2.65/1.02  unif_index_cands_time:                  0.
% 2.65/1.02  unif_index_add_time:                    0.
% 2.65/1.02  orderings_time:                         0.
% 2.65/1.02  out_proof_time:                         0.008
% 2.65/1.02  total_time:                             0.168
% 2.65/1.02  num_of_symbols:                         51
% 2.65/1.02  num_of_terms:                           5275
% 2.65/1.02  
% 2.65/1.02  ------ Preprocessing
% 2.65/1.02  
% 2.65/1.02  num_of_splits:                          0
% 2.65/1.02  num_of_split_atoms:                     0
% 2.65/1.02  num_of_reused_defs:                     0
% 2.65/1.02  num_eq_ax_congr_red:                    27
% 2.65/1.02  num_of_sem_filtered_clauses:            1
% 2.65/1.02  num_of_subtypes:                        0
% 2.65/1.02  monotx_restored_types:                  0
% 2.65/1.02  sat_num_of_epr_types:                   0
% 2.65/1.02  sat_num_of_non_cyclic_types:            0
% 2.65/1.02  sat_guarded_non_collapsed_types:        0
% 2.65/1.02  num_pure_diseq_elim:                    0
% 2.65/1.02  simp_replaced_by:                       0
% 2.65/1.02  res_preprocessed:                       137
% 2.65/1.02  prep_upred:                             0
% 2.65/1.02  prep_unflattend:                        45
% 2.65/1.02  smt_new_axioms:                         0
% 2.65/1.02  pred_elim_cands:                        4
% 2.65/1.02  pred_elim:                              3
% 2.65/1.02  pred_elim_cl:                           4
% 2.65/1.02  pred_elim_cycles:                       7
% 2.65/1.02  merged_defs:                            0
% 2.65/1.02  merged_defs_ncl:                        0
% 2.65/1.02  bin_hyper_res:                          0
% 2.65/1.02  prep_cycles:                            4
% 2.65/1.02  pred_elim_time:                         0.006
% 2.65/1.02  splitting_time:                         0.
% 2.65/1.02  sem_filter_time:                        0.
% 2.65/1.02  monotx_time:                            0.
% 2.65/1.02  subtype_inf_time:                       0.
% 2.65/1.02  
% 2.65/1.02  ------ Problem properties
% 2.65/1.02  
% 2.65/1.02  clauses:                                27
% 2.65/1.02  conjectures:                            3
% 2.65/1.02  epr:                                    3
% 2.65/1.02  horn:                                   21
% 2.65/1.02  ground:                                 6
% 2.65/1.02  unary:                                  7
% 2.65/1.02  binary:                                 4
% 2.65/1.02  lits:                                   68
% 2.65/1.02  lits_eq:                                24
% 2.65/1.02  fd_pure:                                0
% 2.65/1.02  fd_pseudo:                              0
% 2.65/1.02  fd_cond:                                0
% 2.65/1.02  fd_pseudo_cond:                         5
% 2.65/1.02  ac_symbols:                             0
% 2.65/1.02  
% 2.65/1.02  ------ Propositional Solver
% 2.65/1.02  
% 2.65/1.02  prop_solver_calls:                      27
% 2.65/1.02  prop_fast_solver_calls:                 924
% 2.65/1.02  smt_solver_calls:                       0
% 2.65/1.02  smt_fast_solver_calls:                  0
% 2.65/1.02  prop_num_of_clauses:                    1595
% 2.65/1.02  prop_preprocess_simplified:             6480
% 2.65/1.02  prop_fo_subsumed:                       13
% 2.65/1.02  prop_solver_time:                       0.
% 2.65/1.02  smt_solver_time:                        0.
% 2.65/1.02  smt_fast_solver_time:                   0.
% 2.65/1.02  prop_fast_solver_time:                  0.
% 2.65/1.02  prop_unsat_core_time:                   0.
% 2.65/1.02  
% 2.65/1.02  ------ QBF
% 2.65/1.02  
% 2.65/1.02  qbf_q_res:                              0
% 2.65/1.02  qbf_num_tautologies:                    0
% 2.65/1.02  qbf_prep_cycles:                        0
% 2.65/1.02  
% 2.65/1.02  ------ BMC1
% 2.65/1.02  
% 2.65/1.02  bmc1_current_bound:                     -1
% 2.65/1.02  bmc1_last_solved_bound:                 -1
% 2.65/1.02  bmc1_unsat_core_size:                   -1
% 2.65/1.02  bmc1_unsat_core_parents_size:           -1
% 2.65/1.02  bmc1_merge_next_fun:                    0
% 2.65/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.65/1.02  
% 2.65/1.02  ------ Instantiation
% 2.65/1.02  
% 2.65/1.02  inst_num_of_clauses:                    520
% 2.65/1.02  inst_num_in_passive:                    157
% 2.65/1.02  inst_num_in_active:                     203
% 2.65/1.02  inst_num_in_unprocessed:                160
% 2.65/1.02  inst_num_of_loops:                      210
% 2.65/1.02  inst_num_of_learning_restarts:          0
% 2.65/1.02  inst_num_moves_active_passive:          5
% 2.65/1.02  inst_lit_activity:                      0
% 2.65/1.02  inst_lit_activity_moves:                0
% 2.65/1.02  inst_num_tautologies:                   0
% 2.65/1.02  inst_num_prop_implied:                  0
% 2.65/1.02  inst_num_existing_simplified:           0
% 2.65/1.02  inst_num_eq_res_simplified:             0
% 2.65/1.02  inst_num_child_elim:                    0
% 2.65/1.02  inst_num_of_dismatching_blockings:      335
% 2.65/1.02  inst_num_of_non_proper_insts:           500
% 2.65/1.02  inst_num_of_duplicates:                 0
% 2.65/1.02  inst_inst_num_from_inst_to_res:         0
% 2.65/1.02  inst_dismatching_checking_time:         0.
% 2.65/1.02  
% 2.65/1.02  ------ Resolution
% 2.65/1.02  
% 2.65/1.02  res_num_of_clauses:                     0
% 2.65/1.02  res_num_in_passive:                     0
% 2.65/1.02  res_num_in_active:                      0
% 2.65/1.02  res_num_of_loops:                       141
% 2.65/1.02  res_forward_subset_subsumed:            79
% 2.65/1.02  res_backward_subset_subsumed:           0
% 2.65/1.02  res_forward_subsumed:                   1
% 2.65/1.02  res_backward_subsumed:                  1
% 2.65/1.02  res_forward_subsumption_resolution:     1
% 2.65/1.02  res_backward_subsumption_resolution:    0
% 2.65/1.02  res_clause_to_clause_subsumption:       101
% 2.65/1.02  res_orphan_elimination:                 0
% 2.65/1.02  res_tautology_del:                      17
% 2.65/1.02  res_num_eq_res_simplified:              0
% 2.65/1.02  res_num_sel_changes:                    0
% 2.65/1.02  res_moves_from_active_to_pass:          0
% 2.65/1.02  
% 2.65/1.02  ------ Superposition
% 2.65/1.02  
% 2.65/1.02  sup_time_total:                         0.
% 2.65/1.02  sup_time_generating:                    0.
% 2.65/1.02  sup_time_sim_full:                      0.
% 2.65/1.02  sup_time_sim_immed:                     0.
% 2.65/1.02  
% 2.65/1.02  sup_num_of_clauses:                     50
% 2.65/1.02  sup_num_in_active:                      38
% 2.65/1.02  sup_num_in_passive:                     12
% 2.65/1.02  sup_num_of_loops:                       41
% 2.65/1.02  sup_fw_superposition:                   26
% 2.65/1.02  sup_bw_superposition:                   18
% 2.65/1.02  sup_immediate_simplified:               3
% 2.65/1.02  sup_given_eliminated:                   0
% 2.65/1.02  comparisons_done:                       0
% 2.65/1.02  comparisons_avoided:                    1
% 2.65/1.02  
% 2.65/1.02  ------ Simplifications
% 2.65/1.02  
% 2.65/1.02  
% 2.65/1.02  sim_fw_subset_subsumed:                 2
% 2.65/1.02  sim_bw_subset_subsumed:                 0
% 2.65/1.02  sim_fw_subsumed:                        1
% 2.65/1.02  sim_bw_subsumed:                        0
% 2.65/1.02  sim_fw_subsumption_res:                 0
% 2.65/1.02  sim_bw_subsumption_res:                 0
% 2.65/1.02  sim_tautology_del:                      1
% 2.65/1.02  sim_eq_tautology_del:                   4
% 2.65/1.02  sim_eq_res_simp:                        0
% 2.65/1.02  sim_fw_demodulated:                     0
% 2.65/1.02  sim_bw_demodulated:                     4
% 2.65/1.02  sim_light_normalised:                   1
% 2.65/1.02  sim_joinable_taut:                      0
% 2.65/1.02  sim_joinable_simp:                      0
% 2.65/1.02  sim_ac_normalised:                      0
% 2.65/1.02  sim_smt_subsumption:                    0
% 2.65/1.02  
%------------------------------------------------------------------------------
