%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:46 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 588 expanded)
%              Number of clauses        :   56 ( 154 expanded)
%              Number of leaves         :   14 ( 134 expanded)
%              Depth                    :   22
%              Number of atoms          :  313 (1932 expanded)
%              Number of equality atoms :  170 ( 797 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X3,k1_tarski(X0),X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK4,k1_tarski(sK1),sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK4,k1_tarski(sK1),sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f29])).

fof(f50,plain,(
    v1_funct_2(sK4,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f62,plain,(
    v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f50,f54])).

fof(f10,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f52,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f32,f54])).

fof(f63,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f57])).

fof(f64,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f63])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k1_enumset1(X0,X0,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f39,f36,f36])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f53,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(definition_unfolding,[],[f53,f54,f54])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_4,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_927,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_322,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_323,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_542,plain,
    ( k1_relset_1(X0,X1,sK4) = X0
    | k1_enumset1(sK1,sK1,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != sK4
    | sK2 != X1
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_323])).

cnf(c_543,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_544,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_17])).

cnf(c_545,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(renaming,[status(thm)],[c_544])).

cnf(c_603,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
    inference(equality_resolution_simp,[status(thm)],[c_545])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_367,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_368,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1029,plain,
    ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_368])).

cnf(c_1100,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_603,c_1029])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_929,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1208,plain,
    ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1100,c_929])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k1_enumset1(X2,X2,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_251,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k1_enumset1(X2,X2,X0))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_252,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ r2_hidden(X1,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k1_enumset1(X0,X0,X1)) ),
    inference(unflattening,[status(thm)],[c_251])).

cnf(c_924,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k1_enumset1(X0,X0,X1))
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_253,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k1_enumset1(X0,X0,X1))
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_724,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1019,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_376,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_377,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_1022,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_1023,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_1667,plain,
    ( r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k1_enumset1(X0,X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_924,c_253,c_1019,c_1023])).

cnf(c_1668,plain,
    ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k1_enumset1(X0,X0,X1))
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1667])).

cnf(c_1897,plain,
    ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k1_enumset1(sK1,sK1,X0))
    | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_1668])).

cnf(c_2314,plain,
    ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k9_relat_1(sK4,k1_enumset1(sK1,sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_1208,c_1897])).

cnf(c_923,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_1201,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_923,c_1019,c_1023])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_926,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1277,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1201,c_926])).

cnf(c_2316,plain,
    ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_2314,c_1100,c_1277])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_925,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1105,plain,
    ( r1_tarski(k7_relset_1(k1_relat_1(sK4),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1100,c_925])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_358,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_18])).

cnf(c_359,plain,
    ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_1061,plain,
    ( k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_359])).

cnf(c_1395,plain,
    ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(light_normalisation,[status(thm)],[c_1061,c_1100])).

cnf(c_1521,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1105,c_1395])).

cnf(c_2408,plain,
    ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2316,c_1521])).

cnf(c_2424,plain,
    ( v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_927,c_2408])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2424,c_1023,c_1019])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:14:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.47/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/0.97  
% 2.47/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.47/0.97  
% 2.47/0.97  ------  iProver source info
% 2.47/0.97  
% 2.47/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.47/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.47/0.97  git: non_committed_changes: false
% 2.47/0.97  git: last_make_outside_of_git: false
% 2.47/0.97  
% 2.47/0.97  ------ 
% 2.47/0.97  
% 2.47/0.97  ------ Input Options
% 2.47/0.97  
% 2.47/0.97  --out_options                           all
% 2.47/0.97  --tptp_safe_out                         true
% 2.47/0.97  --problem_path                          ""
% 2.47/0.97  --include_path                          ""
% 2.47/0.97  --clausifier                            res/vclausify_rel
% 2.47/0.97  --clausifier_options                    --mode clausify
% 2.47/0.97  --stdin                                 false
% 2.47/0.97  --stats_out                             all
% 2.47/0.97  
% 2.47/0.97  ------ General Options
% 2.47/0.97  
% 2.47/0.97  --fof                                   false
% 2.47/0.97  --time_out_real                         305.
% 2.47/0.97  --time_out_virtual                      -1.
% 2.47/0.97  --symbol_type_check                     false
% 2.47/0.97  --clausify_out                          false
% 2.47/0.97  --sig_cnt_out                           false
% 2.47/0.97  --trig_cnt_out                          false
% 2.47/0.97  --trig_cnt_out_tolerance                1.
% 2.47/0.97  --trig_cnt_out_sk_spl                   false
% 2.47/0.97  --abstr_cl_out                          false
% 2.47/0.97  
% 2.47/0.97  ------ Global Options
% 2.47/0.97  
% 2.47/0.97  --schedule                              default
% 2.47/0.97  --add_important_lit                     false
% 2.47/0.97  --prop_solver_per_cl                    1000
% 2.47/0.97  --min_unsat_core                        false
% 2.47/0.97  --soft_assumptions                      false
% 2.47/0.97  --soft_lemma_size                       3
% 2.47/0.97  --prop_impl_unit_size                   0
% 2.47/0.97  --prop_impl_unit                        []
% 2.47/0.97  --share_sel_clauses                     true
% 2.47/0.97  --reset_solvers                         false
% 2.47/0.97  --bc_imp_inh                            [conj_cone]
% 2.47/0.97  --conj_cone_tolerance                   3.
% 2.47/0.97  --extra_neg_conj                        none
% 2.47/0.97  --large_theory_mode                     true
% 2.47/0.97  --prolific_symb_bound                   200
% 2.47/0.97  --lt_threshold                          2000
% 2.47/0.97  --clause_weak_htbl                      true
% 2.47/0.97  --gc_record_bc_elim                     false
% 2.47/0.97  
% 2.47/0.97  ------ Preprocessing Options
% 2.47/0.97  
% 2.47/0.97  --preprocessing_flag                    true
% 2.47/0.97  --time_out_prep_mult                    0.1
% 2.47/0.97  --splitting_mode                        input
% 2.47/0.97  --splitting_grd                         true
% 2.47/0.97  --splitting_cvd                         false
% 2.47/0.97  --splitting_cvd_svl                     false
% 2.47/0.97  --splitting_nvd                         32
% 2.47/0.97  --sub_typing                            true
% 2.47/0.97  --prep_gs_sim                           true
% 2.47/0.97  --prep_unflatten                        true
% 2.47/0.97  --prep_res_sim                          true
% 2.47/0.97  --prep_upred                            true
% 2.47/0.97  --prep_sem_filter                       exhaustive
% 2.47/0.97  --prep_sem_filter_out                   false
% 2.47/0.97  --pred_elim                             true
% 2.47/0.97  --res_sim_input                         true
% 2.47/0.97  --eq_ax_congr_red                       true
% 2.47/0.97  --pure_diseq_elim                       true
% 2.47/0.97  --brand_transform                       false
% 2.47/0.97  --non_eq_to_eq                          false
% 2.47/0.97  --prep_def_merge                        true
% 2.47/0.97  --prep_def_merge_prop_impl              false
% 2.47/0.97  --prep_def_merge_mbd                    true
% 2.47/0.97  --prep_def_merge_tr_red                 false
% 2.47/0.97  --prep_def_merge_tr_cl                  false
% 2.47/0.97  --smt_preprocessing                     true
% 2.47/0.97  --smt_ac_axioms                         fast
% 2.47/0.97  --preprocessed_out                      false
% 2.47/0.97  --preprocessed_stats                    false
% 2.47/0.97  
% 2.47/0.97  ------ Abstraction refinement Options
% 2.47/0.97  
% 2.47/0.97  --abstr_ref                             []
% 2.47/0.97  --abstr_ref_prep                        false
% 2.47/0.97  --abstr_ref_until_sat                   false
% 2.47/0.97  --abstr_ref_sig_restrict                funpre
% 2.47/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/0.97  --abstr_ref_under                       []
% 2.47/0.97  
% 2.47/0.97  ------ SAT Options
% 2.47/0.97  
% 2.47/0.97  --sat_mode                              false
% 2.47/0.97  --sat_fm_restart_options                ""
% 2.47/0.97  --sat_gr_def                            false
% 2.47/0.97  --sat_epr_types                         true
% 2.47/0.97  --sat_non_cyclic_types                  false
% 2.47/0.97  --sat_finite_models                     false
% 2.47/0.97  --sat_fm_lemmas                         false
% 2.47/0.97  --sat_fm_prep                           false
% 2.47/0.97  --sat_fm_uc_incr                        true
% 2.47/0.97  --sat_out_model                         small
% 2.47/0.97  --sat_out_clauses                       false
% 2.47/0.97  
% 2.47/0.97  ------ QBF Options
% 2.47/0.97  
% 2.47/0.97  --qbf_mode                              false
% 2.47/0.97  --qbf_elim_univ                         false
% 2.47/0.97  --qbf_dom_inst                          none
% 2.47/0.97  --qbf_dom_pre_inst                      false
% 2.47/0.97  --qbf_sk_in                             false
% 2.47/0.97  --qbf_pred_elim                         true
% 2.47/0.97  --qbf_split                             512
% 2.47/0.97  
% 2.47/0.97  ------ BMC1 Options
% 2.47/0.97  
% 2.47/0.97  --bmc1_incremental                      false
% 2.47/0.97  --bmc1_axioms                           reachable_all
% 2.47/0.97  --bmc1_min_bound                        0
% 2.47/0.97  --bmc1_max_bound                        -1
% 2.47/0.97  --bmc1_max_bound_default                -1
% 2.47/0.97  --bmc1_symbol_reachability              true
% 2.47/0.97  --bmc1_property_lemmas                  false
% 2.47/0.97  --bmc1_k_induction                      false
% 2.47/0.97  --bmc1_non_equiv_states                 false
% 2.47/0.97  --bmc1_deadlock                         false
% 2.47/0.97  --bmc1_ucm                              false
% 2.47/0.97  --bmc1_add_unsat_core                   none
% 2.47/0.97  --bmc1_unsat_core_children              false
% 2.47/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/0.97  --bmc1_out_stat                         full
% 2.47/0.97  --bmc1_ground_init                      false
% 2.47/0.97  --bmc1_pre_inst_next_state              false
% 2.47/0.97  --bmc1_pre_inst_state                   false
% 2.47/0.97  --bmc1_pre_inst_reach_state             false
% 2.47/0.97  --bmc1_out_unsat_core                   false
% 2.47/0.97  --bmc1_aig_witness_out                  false
% 2.47/0.97  --bmc1_verbose                          false
% 2.47/0.97  --bmc1_dump_clauses_tptp                false
% 2.47/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.47/0.97  --bmc1_dump_file                        -
% 2.47/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.47/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.47/0.97  --bmc1_ucm_extend_mode                  1
% 2.47/0.97  --bmc1_ucm_init_mode                    2
% 2.47/0.97  --bmc1_ucm_cone_mode                    none
% 2.47/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.47/0.97  --bmc1_ucm_relax_model                  4
% 2.47/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.47/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/0.97  --bmc1_ucm_layered_model                none
% 2.47/0.97  --bmc1_ucm_max_lemma_size               10
% 2.47/0.97  
% 2.47/0.97  ------ AIG Options
% 2.47/0.97  
% 2.47/0.97  --aig_mode                              false
% 2.47/0.97  
% 2.47/0.97  ------ Instantiation Options
% 2.47/0.97  
% 2.47/0.97  --instantiation_flag                    true
% 2.47/0.97  --inst_sos_flag                         false
% 2.47/0.97  --inst_sos_phase                        true
% 2.47/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/0.97  --inst_lit_sel_side                     num_symb
% 2.47/0.97  --inst_solver_per_active                1400
% 2.47/0.97  --inst_solver_calls_frac                1.
% 2.47/0.97  --inst_passive_queue_type               priority_queues
% 2.47/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/0.97  --inst_passive_queues_freq              [25;2]
% 2.47/0.97  --inst_dismatching                      true
% 2.47/0.97  --inst_eager_unprocessed_to_passive     true
% 2.47/0.97  --inst_prop_sim_given                   true
% 2.47/0.97  --inst_prop_sim_new                     false
% 2.47/0.97  --inst_subs_new                         false
% 2.47/0.97  --inst_eq_res_simp                      false
% 2.47/0.97  --inst_subs_given                       false
% 2.47/0.97  --inst_orphan_elimination               true
% 2.47/0.97  --inst_learning_loop_flag               true
% 2.47/0.97  --inst_learning_start                   3000
% 2.47/0.97  --inst_learning_factor                  2
% 2.47/0.97  --inst_start_prop_sim_after_learn       3
% 2.47/0.97  --inst_sel_renew                        solver
% 2.47/0.97  --inst_lit_activity_flag                true
% 2.47/0.97  --inst_restr_to_given                   false
% 2.47/0.97  --inst_activity_threshold               500
% 2.47/0.97  --inst_out_proof                        true
% 2.47/0.97  
% 2.47/0.97  ------ Resolution Options
% 2.47/0.97  
% 2.47/0.97  --resolution_flag                       true
% 2.47/0.97  --res_lit_sel                           adaptive
% 2.47/0.97  --res_lit_sel_side                      none
% 2.47/0.97  --res_ordering                          kbo
% 2.47/0.97  --res_to_prop_solver                    active
% 2.47/0.97  --res_prop_simpl_new                    false
% 2.47/0.97  --res_prop_simpl_given                  true
% 2.47/0.97  --res_passive_queue_type                priority_queues
% 2.47/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/0.97  --res_passive_queues_freq               [15;5]
% 2.47/0.97  --res_forward_subs                      full
% 2.47/0.97  --res_backward_subs                     full
% 2.47/0.97  --res_forward_subs_resolution           true
% 2.47/0.97  --res_backward_subs_resolution          true
% 2.47/0.97  --res_orphan_elimination                true
% 2.47/0.97  --res_time_limit                        2.
% 2.47/0.97  --res_out_proof                         true
% 2.47/0.97  
% 2.47/0.97  ------ Superposition Options
% 2.47/0.97  
% 2.47/0.97  --superposition_flag                    true
% 2.47/0.97  --sup_passive_queue_type                priority_queues
% 2.47/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.47/0.97  --demod_completeness_check              fast
% 2.47/0.97  --demod_use_ground                      true
% 2.47/0.97  --sup_to_prop_solver                    passive
% 2.47/0.97  --sup_prop_simpl_new                    true
% 2.47/0.97  --sup_prop_simpl_given                  true
% 2.47/0.97  --sup_fun_splitting                     false
% 2.47/0.97  --sup_smt_interval                      50000
% 2.47/0.97  
% 2.47/0.97  ------ Superposition Simplification Setup
% 2.47/0.97  
% 2.47/0.97  --sup_indices_passive                   []
% 2.47/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.97  --sup_full_bw                           [BwDemod]
% 2.47/0.97  --sup_immed_triv                        [TrivRules]
% 2.47/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.97  --sup_immed_bw_main                     []
% 2.47/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.97  
% 2.47/0.97  ------ Combination Options
% 2.47/0.97  
% 2.47/0.97  --comb_res_mult                         3
% 2.47/0.97  --comb_sup_mult                         2
% 2.47/0.97  --comb_inst_mult                        10
% 2.47/0.97  
% 2.47/0.97  ------ Debug Options
% 2.47/0.97  
% 2.47/0.97  --dbg_backtrace                         false
% 2.47/0.97  --dbg_dump_prop_clauses                 false
% 2.47/0.97  --dbg_dump_prop_clauses_file            -
% 2.47/0.97  --dbg_out_stat                          false
% 2.47/0.97  ------ Parsing...
% 2.47/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.47/0.97  
% 2.47/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.47/0.97  
% 2.47/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.47/0.97  
% 2.47/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.47/0.97  ------ Proving...
% 2.47/0.97  ------ Problem Properties 
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  clauses                                 15
% 2.47/0.97  conjectures                             2
% 2.47/0.97  EPR                                     1
% 2.47/0.97  Horn                                    13
% 2.47/0.97  unary                                   4
% 2.47/0.97  binary                                  6
% 2.47/0.97  lits                                    33
% 2.47/0.97  lits eq                                 21
% 2.47/0.97  fd_pure                                 0
% 2.47/0.97  fd_pseudo                               0
% 2.47/0.97  fd_cond                                 0
% 2.47/0.97  fd_pseudo_cond                          2
% 2.47/0.97  AC symbols                              0
% 2.47/0.97  
% 2.47/0.97  ------ Schedule dynamic 5 is on 
% 2.47/0.97  
% 2.47/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  ------ 
% 2.47/0.97  Current options:
% 2.47/0.97  ------ 
% 2.47/0.97  
% 2.47/0.97  ------ Input Options
% 2.47/0.97  
% 2.47/0.97  --out_options                           all
% 2.47/0.97  --tptp_safe_out                         true
% 2.47/0.97  --problem_path                          ""
% 2.47/0.97  --include_path                          ""
% 2.47/0.97  --clausifier                            res/vclausify_rel
% 2.47/0.97  --clausifier_options                    --mode clausify
% 2.47/0.97  --stdin                                 false
% 2.47/0.97  --stats_out                             all
% 2.47/0.97  
% 2.47/0.97  ------ General Options
% 2.47/0.97  
% 2.47/0.97  --fof                                   false
% 2.47/0.97  --time_out_real                         305.
% 2.47/0.97  --time_out_virtual                      -1.
% 2.47/0.97  --symbol_type_check                     false
% 2.47/0.97  --clausify_out                          false
% 2.47/0.97  --sig_cnt_out                           false
% 2.47/0.97  --trig_cnt_out                          false
% 2.47/0.97  --trig_cnt_out_tolerance                1.
% 2.47/0.97  --trig_cnt_out_sk_spl                   false
% 2.47/0.97  --abstr_cl_out                          false
% 2.47/0.97  
% 2.47/0.97  ------ Global Options
% 2.47/0.97  
% 2.47/0.97  --schedule                              default
% 2.47/0.97  --add_important_lit                     false
% 2.47/0.97  --prop_solver_per_cl                    1000
% 2.47/0.97  --min_unsat_core                        false
% 2.47/0.97  --soft_assumptions                      false
% 2.47/0.97  --soft_lemma_size                       3
% 2.47/0.97  --prop_impl_unit_size                   0
% 2.47/0.97  --prop_impl_unit                        []
% 2.47/0.97  --share_sel_clauses                     true
% 2.47/0.97  --reset_solvers                         false
% 2.47/0.97  --bc_imp_inh                            [conj_cone]
% 2.47/0.97  --conj_cone_tolerance                   3.
% 2.47/0.97  --extra_neg_conj                        none
% 2.47/0.97  --large_theory_mode                     true
% 2.47/0.97  --prolific_symb_bound                   200
% 2.47/0.97  --lt_threshold                          2000
% 2.47/0.97  --clause_weak_htbl                      true
% 2.47/0.97  --gc_record_bc_elim                     false
% 2.47/0.97  
% 2.47/0.97  ------ Preprocessing Options
% 2.47/0.97  
% 2.47/0.97  --preprocessing_flag                    true
% 2.47/0.97  --time_out_prep_mult                    0.1
% 2.47/0.97  --splitting_mode                        input
% 2.47/0.97  --splitting_grd                         true
% 2.47/0.97  --splitting_cvd                         false
% 2.47/0.97  --splitting_cvd_svl                     false
% 2.47/0.97  --splitting_nvd                         32
% 2.47/0.97  --sub_typing                            true
% 2.47/0.97  --prep_gs_sim                           true
% 2.47/0.97  --prep_unflatten                        true
% 2.47/0.97  --prep_res_sim                          true
% 2.47/0.97  --prep_upred                            true
% 2.47/0.97  --prep_sem_filter                       exhaustive
% 2.47/0.97  --prep_sem_filter_out                   false
% 2.47/0.97  --pred_elim                             true
% 2.47/0.97  --res_sim_input                         true
% 2.47/0.97  --eq_ax_congr_red                       true
% 2.47/0.97  --pure_diseq_elim                       true
% 2.47/0.97  --brand_transform                       false
% 2.47/0.97  --non_eq_to_eq                          false
% 2.47/0.97  --prep_def_merge                        true
% 2.47/0.97  --prep_def_merge_prop_impl              false
% 2.47/0.97  --prep_def_merge_mbd                    true
% 2.47/0.97  --prep_def_merge_tr_red                 false
% 2.47/0.97  --prep_def_merge_tr_cl                  false
% 2.47/0.97  --smt_preprocessing                     true
% 2.47/0.97  --smt_ac_axioms                         fast
% 2.47/0.97  --preprocessed_out                      false
% 2.47/0.97  --preprocessed_stats                    false
% 2.47/0.97  
% 2.47/0.97  ------ Abstraction refinement Options
% 2.47/0.97  
% 2.47/0.97  --abstr_ref                             []
% 2.47/0.97  --abstr_ref_prep                        false
% 2.47/0.97  --abstr_ref_until_sat                   false
% 2.47/0.97  --abstr_ref_sig_restrict                funpre
% 2.47/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/0.97  --abstr_ref_under                       []
% 2.47/0.97  
% 2.47/0.97  ------ SAT Options
% 2.47/0.97  
% 2.47/0.97  --sat_mode                              false
% 2.47/0.97  --sat_fm_restart_options                ""
% 2.47/0.97  --sat_gr_def                            false
% 2.47/0.97  --sat_epr_types                         true
% 2.47/0.97  --sat_non_cyclic_types                  false
% 2.47/0.97  --sat_finite_models                     false
% 2.47/0.97  --sat_fm_lemmas                         false
% 2.47/0.97  --sat_fm_prep                           false
% 2.47/0.97  --sat_fm_uc_incr                        true
% 2.47/0.97  --sat_out_model                         small
% 2.47/0.97  --sat_out_clauses                       false
% 2.47/0.97  
% 2.47/0.97  ------ QBF Options
% 2.47/0.97  
% 2.47/0.97  --qbf_mode                              false
% 2.47/0.97  --qbf_elim_univ                         false
% 2.47/0.97  --qbf_dom_inst                          none
% 2.47/0.97  --qbf_dom_pre_inst                      false
% 2.47/0.97  --qbf_sk_in                             false
% 2.47/0.97  --qbf_pred_elim                         true
% 2.47/0.97  --qbf_split                             512
% 2.47/0.97  
% 2.47/0.97  ------ BMC1 Options
% 2.47/0.97  
% 2.47/0.97  --bmc1_incremental                      false
% 2.47/0.97  --bmc1_axioms                           reachable_all
% 2.47/0.97  --bmc1_min_bound                        0
% 2.47/0.97  --bmc1_max_bound                        -1
% 2.47/0.97  --bmc1_max_bound_default                -1
% 2.47/0.97  --bmc1_symbol_reachability              true
% 2.47/0.97  --bmc1_property_lemmas                  false
% 2.47/0.97  --bmc1_k_induction                      false
% 2.47/0.97  --bmc1_non_equiv_states                 false
% 2.47/0.97  --bmc1_deadlock                         false
% 2.47/0.97  --bmc1_ucm                              false
% 2.47/0.97  --bmc1_add_unsat_core                   none
% 2.47/0.97  --bmc1_unsat_core_children              false
% 2.47/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/0.97  --bmc1_out_stat                         full
% 2.47/0.97  --bmc1_ground_init                      false
% 2.47/0.97  --bmc1_pre_inst_next_state              false
% 2.47/0.97  --bmc1_pre_inst_state                   false
% 2.47/0.97  --bmc1_pre_inst_reach_state             false
% 2.47/0.97  --bmc1_out_unsat_core                   false
% 2.47/0.97  --bmc1_aig_witness_out                  false
% 2.47/0.97  --bmc1_verbose                          false
% 2.47/0.97  --bmc1_dump_clauses_tptp                false
% 2.47/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.47/0.97  --bmc1_dump_file                        -
% 2.47/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.47/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.47/0.97  --bmc1_ucm_extend_mode                  1
% 2.47/0.97  --bmc1_ucm_init_mode                    2
% 2.47/0.97  --bmc1_ucm_cone_mode                    none
% 2.47/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.47/0.97  --bmc1_ucm_relax_model                  4
% 2.47/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.47/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/0.97  --bmc1_ucm_layered_model                none
% 2.47/0.97  --bmc1_ucm_max_lemma_size               10
% 2.47/0.97  
% 2.47/0.97  ------ AIG Options
% 2.47/0.97  
% 2.47/0.97  --aig_mode                              false
% 2.47/0.97  
% 2.47/0.97  ------ Instantiation Options
% 2.47/0.97  
% 2.47/0.97  --instantiation_flag                    true
% 2.47/0.97  --inst_sos_flag                         false
% 2.47/0.97  --inst_sos_phase                        true
% 2.47/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/0.97  --inst_lit_sel_side                     none
% 2.47/0.97  --inst_solver_per_active                1400
% 2.47/0.97  --inst_solver_calls_frac                1.
% 2.47/0.97  --inst_passive_queue_type               priority_queues
% 2.47/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/0.97  --inst_passive_queues_freq              [25;2]
% 2.47/0.97  --inst_dismatching                      true
% 2.47/0.97  --inst_eager_unprocessed_to_passive     true
% 2.47/0.97  --inst_prop_sim_given                   true
% 2.47/0.97  --inst_prop_sim_new                     false
% 2.47/0.97  --inst_subs_new                         false
% 2.47/0.97  --inst_eq_res_simp                      false
% 2.47/0.97  --inst_subs_given                       false
% 2.47/0.97  --inst_orphan_elimination               true
% 2.47/0.97  --inst_learning_loop_flag               true
% 2.47/0.97  --inst_learning_start                   3000
% 2.47/0.97  --inst_learning_factor                  2
% 2.47/0.97  --inst_start_prop_sim_after_learn       3
% 2.47/0.97  --inst_sel_renew                        solver
% 2.47/0.97  --inst_lit_activity_flag                true
% 2.47/0.97  --inst_restr_to_given                   false
% 2.47/0.97  --inst_activity_threshold               500
% 2.47/0.97  --inst_out_proof                        true
% 2.47/0.97  
% 2.47/0.97  ------ Resolution Options
% 2.47/0.97  
% 2.47/0.97  --resolution_flag                       false
% 2.47/0.97  --res_lit_sel                           adaptive
% 2.47/0.97  --res_lit_sel_side                      none
% 2.47/0.97  --res_ordering                          kbo
% 2.47/0.97  --res_to_prop_solver                    active
% 2.47/0.97  --res_prop_simpl_new                    false
% 2.47/0.97  --res_prop_simpl_given                  true
% 2.47/0.97  --res_passive_queue_type                priority_queues
% 2.47/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/0.97  --res_passive_queues_freq               [15;5]
% 2.47/0.97  --res_forward_subs                      full
% 2.47/0.97  --res_backward_subs                     full
% 2.47/0.97  --res_forward_subs_resolution           true
% 2.47/0.97  --res_backward_subs_resolution          true
% 2.47/0.97  --res_orphan_elimination                true
% 2.47/0.97  --res_time_limit                        2.
% 2.47/0.97  --res_out_proof                         true
% 2.47/0.97  
% 2.47/0.97  ------ Superposition Options
% 2.47/0.97  
% 2.47/0.97  --superposition_flag                    true
% 2.47/0.97  --sup_passive_queue_type                priority_queues
% 2.47/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.47/0.97  --demod_completeness_check              fast
% 2.47/0.97  --demod_use_ground                      true
% 2.47/0.97  --sup_to_prop_solver                    passive
% 2.47/0.97  --sup_prop_simpl_new                    true
% 2.47/0.97  --sup_prop_simpl_given                  true
% 2.47/0.97  --sup_fun_splitting                     false
% 2.47/0.97  --sup_smt_interval                      50000
% 2.47/0.97  
% 2.47/0.97  ------ Superposition Simplification Setup
% 2.47/0.97  
% 2.47/0.97  --sup_indices_passive                   []
% 2.47/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.97  --sup_full_bw                           [BwDemod]
% 2.47/0.97  --sup_immed_triv                        [TrivRules]
% 2.47/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.97  --sup_immed_bw_main                     []
% 2.47/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/0.97  
% 2.47/0.97  ------ Combination Options
% 2.47/0.97  
% 2.47/0.97  --comb_res_mult                         3
% 2.47/0.97  --comb_sup_mult                         2
% 2.47/0.97  --comb_inst_mult                        10
% 2.47/0.97  
% 2.47/0.97  ------ Debug Options
% 2.47/0.97  
% 2.47/0.97  --dbg_backtrace                         false
% 2.47/0.97  --dbg_dump_prop_clauses                 false
% 2.47/0.97  --dbg_dump_prop_clauses_file            -
% 2.47/0.97  --dbg_out_stat                          false
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  ------ Proving...
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  % SZS status Theorem for theBenchmark.p
% 2.47/0.97  
% 2.47/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.47/0.97  
% 2.47/0.97  fof(f4,axiom,(
% 2.47/0.97    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.47/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f13,plain,(
% 2.47/0.97    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.47/0.97    inference(ennf_transformation,[],[f4])).
% 2.47/0.97  
% 2.47/0.97  fof(f37,plain,(
% 2.47/0.97    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.47/0.97    inference(cnf_transformation,[],[f13])).
% 2.47/0.97  
% 2.47/0.97  fof(f11,conjecture,(
% 2.47/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.47/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f12,negated_conjecture,(
% 2.47/0.97    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.47/0.97    inference(negated_conjecture,[],[f11])).
% 2.47/0.97  
% 2.47/0.97  fof(f22,plain,(
% 2.47/0.97    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)))),
% 2.47/0.97    inference(ennf_transformation,[],[f12])).
% 2.47/0.97  
% 2.47/0.97  fof(f23,plain,(
% 2.47/0.97    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3))),
% 2.47/0.97    inference(flattening,[],[f22])).
% 2.47/0.97  
% 2.47/0.97  fof(f29,plain,(
% 2.47/0.97    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4))),
% 2.47/0.97    introduced(choice_axiom,[])).
% 2.47/0.97  
% 2.47/0.97  fof(f30,plain,(
% 2.47/0.97    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1))) & k1_xboole_0 != sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK4,k1_tarski(sK1),sK2) & v1_funct_1(sK4)),
% 2.47/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f23,f29])).
% 2.47/0.97  
% 2.47/0.97  fof(f50,plain,(
% 2.47/0.97    v1_funct_2(sK4,k1_tarski(sK1),sK2)),
% 2.47/0.97    inference(cnf_transformation,[],[f30])).
% 2.47/0.97  
% 2.47/0.97  fof(f2,axiom,(
% 2.47/0.97    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.47/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f35,plain,(
% 2.47/0.97    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.47/0.97    inference(cnf_transformation,[],[f2])).
% 2.47/0.97  
% 2.47/0.97  fof(f3,axiom,(
% 2.47/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.47/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f36,plain,(
% 2.47/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.47/0.97    inference(cnf_transformation,[],[f3])).
% 2.47/0.97  
% 2.47/0.97  fof(f54,plain,(
% 2.47/0.97    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.47/0.97    inference(definition_unfolding,[],[f35,f36])).
% 2.47/0.97  
% 2.47/0.97  fof(f62,plain,(
% 2.47/0.97    v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2)),
% 2.47/0.97    inference(definition_unfolding,[],[f50,f54])).
% 2.47/0.97  
% 2.47/0.97  fof(f10,axiom,(
% 2.47/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.47/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f20,plain,(
% 2.47/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.47/0.97    inference(ennf_transformation,[],[f10])).
% 2.47/0.97  
% 2.47/0.97  fof(f21,plain,(
% 2.47/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.47/0.97    inference(flattening,[],[f20])).
% 2.47/0.97  
% 2.47/0.97  fof(f28,plain,(
% 2.47/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.47/0.97    inference(nnf_transformation,[],[f21])).
% 2.47/0.97  
% 2.47/0.97  fof(f43,plain,(
% 2.47/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.47/0.97    inference(cnf_transformation,[],[f28])).
% 2.47/0.97  
% 2.47/0.97  fof(f51,plain,(
% 2.47/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 2.47/0.97    inference(cnf_transformation,[],[f30])).
% 2.47/0.97  
% 2.47/0.97  fof(f61,plain,(
% 2.47/0.97    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)))),
% 2.47/0.97    inference(definition_unfolding,[],[f51,f54])).
% 2.47/0.97  
% 2.47/0.97  fof(f52,plain,(
% 2.47/0.97    k1_xboole_0 != sK2),
% 2.47/0.97    inference(cnf_transformation,[],[f30])).
% 2.47/0.97  
% 2.47/0.97  fof(f8,axiom,(
% 2.47/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.47/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f18,plain,(
% 2.47/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.47/0.97    inference(ennf_transformation,[],[f8])).
% 2.47/0.97  
% 2.47/0.97  fof(f41,plain,(
% 2.47/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.47/0.97    inference(cnf_transformation,[],[f18])).
% 2.47/0.97  
% 2.47/0.97  fof(f1,axiom,(
% 2.47/0.97    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.47/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f24,plain,(
% 2.47/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.47/0.97    inference(nnf_transformation,[],[f1])).
% 2.47/0.97  
% 2.47/0.97  fof(f25,plain,(
% 2.47/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.47/0.97    inference(rectify,[],[f24])).
% 2.47/0.97  
% 2.47/0.97  fof(f26,plain,(
% 2.47/0.97    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 2.47/0.97    introduced(choice_axiom,[])).
% 2.47/0.97  
% 2.47/0.97  fof(f27,plain,(
% 2.47/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.47/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 2.47/0.97  
% 2.47/0.97  fof(f32,plain,(
% 2.47/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.47/0.97    inference(cnf_transformation,[],[f27])).
% 2.47/0.97  
% 2.47/0.97  fof(f57,plain,(
% 2.47/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 2.47/0.97    inference(definition_unfolding,[],[f32,f54])).
% 2.47/0.97  
% 2.47/0.97  fof(f63,plain,(
% 2.47/0.97    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 2.47/0.97    inference(equality_resolution,[],[f57])).
% 2.47/0.97  
% 2.47/0.97  fof(f64,plain,(
% 2.47/0.97    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 2.47/0.97    inference(equality_resolution,[],[f63])).
% 2.47/0.97  
% 2.47/0.97  fof(f6,axiom,(
% 2.47/0.97    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1))))),
% 2.47/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f15,plain,(
% 2.47/0.97    ! [X0,X1,X2] : ((k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.47/0.97    inference(ennf_transformation,[],[f6])).
% 2.47/0.97  
% 2.47/0.97  fof(f16,plain,(
% 2.47/0.97    ! [X0,X1,X2] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.47/0.97    inference(flattening,[],[f15])).
% 2.47/0.97  
% 2.47/0.97  fof(f39,plain,(
% 2.47/0.97    ( ! [X2,X0,X1] : (k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k2_tarski(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.47/0.97    inference(cnf_transformation,[],[f16])).
% 2.47/0.97  
% 2.47/0.97  fof(f59,plain,(
% 2.47/0.97    ( ! [X2,X0,X1] : (k1_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X1)) = k9_relat_1(X2,k1_enumset1(X0,X0,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.47/0.97    inference(definition_unfolding,[],[f39,f36,f36])).
% 2.47/0.97  
% 2.47/0.97  fof(f49,plain,(
% 2.47/0.97    v1_funct_1(sK4)),
% 2.47/0.97    inference(cnf_transformation,[],[f30])).
% 2.47/0.97  
% 2.47/0.97  fof(f7,axiom,(
% 2.47/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.47/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f17,plain,(
% 2.47/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.47/0.97    inference(ennf_transformation,[],[f7])).
% 2.47/0.97  
% 2.47/0.97  fof(f40,plain,(
% 2.47/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.47/0.97    inference(cnf_transformation,[],[f17])).
% 2.47/0.97  
% 2.47/0.97  fof(f5,axiom,(
% 2.47/0.97    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.47/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f14,plain,(
% 2.47/0.97    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.47/0.97    inference(ennf_transformation,[],[f5])).
% 2.47/0.97  
% 2.47/0.97  fof(f38,plain,(
% 2.47/0.97    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.47/0.97    inference(cnf_transformation,[],[f14])).
% 2.47/0.97  
% 2.47/0.97  fof(f53,plain,(
% 2.47/0.97    ~r1_tarski(k7_relset_1(k1_tarski(sK1),sK2,sK4,sK3),k1_tarski(k1_funct_1(sK4,sK1)))),
% 2.47/0.97    inference(cnf_transformation,[],[f30])).
% 2.47/0.97  
% 2.47/0.97  fof(f60,plain,(
% 2.47/0.97    ~r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)))),
% 2.47/0.97    inference(definition_unfolding,[],[f53,f54,f54])).
% 2.47/0.97  
% 2.47/0.97  fof(f9,axiom,(
% 2.47/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.47/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/0.97  
% 2.47/0.97  fof(f19,plain,(
% 2.47/0.97    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.47/0.97    inference(ennf_transformation,[],[f9])).
% 2.47/0.97  
% 2.47/0.97  fof(f42,plain,(
% 2.47/0.97    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.47/0.97    inference(cnf_transformation,[],[f19])).
% 2.47/0.97  
% 2.47/0.97  cnf(c_4,plain,
% 2.47/0.97      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.47/0.97      inference(cnf_transformation,[],[f37]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_927,plain,
% 2.47/0.97      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 2.47/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_19,negated_conjecture,
% 2.47/0.97      ( v1_funct_2(sK4,k1_enumset1(sK1,sK1,sK1),sK2) ),
% 2.47/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_15,plain,
% 2.47/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.47/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.47/0.97      | k1_relset_1(X1,X2,X0) = X1
% 2.47/0.97      | k1_xboole_0 = X2 ),
% 2.47/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_18,negated_conjecture,
% 2.47/0.97      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))) ),
% 2.47/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_322,plain,
% 2.47/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.47/0.97      | k1_relset_1(X1,X2,X0) = X1
% 2.47/0.97      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.47/0.97      | sK4 != X0
% 2.47/0.97      | k1_xboole_0 = X2 ),
% 2.47/0.97      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_323,plain,
% 2.47/0.97      ( ~ v1_funct_2(sK4,X0,X1)
% 2.47/0.97      | k1_relset_1(X0,X1,sK4) = X0
% 2.47/0.97      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.47/0.97      | k1_xboole_0 = X1 ),
% 2.47/0.97      inference(unflattening,[status(thm)],[c_322]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_542,plain,
% 2.47/0.97      ( k1_relset_1(X0,X1,sK4) = X0
% 2.47/0.97      | k1_enumset1(sK1,sK1,sK1) != X0
% 2.47/0.97      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.47/0.97      | sK4 != sK4
% 2.47/0.97      | sK2 != X1
% 2.47/0.97      | k1_xboole_0 = X1 ),
% 2.47/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_323]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_543,plain,
% 2.47/0.97      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
% 2.47/0.97      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.47/0.97      | k1_xboole_0 = sK2 ),
% 2.47/0.97      inference(unflattening,[status(thm)],[c_542]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_17,negated_conjecture,
% 2.47/0.97      ( k1_xboole_0 != sK2 ),
% 2.47/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_544,plain,
% 2.47/0.97      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.47/0.97      | k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
% 2.47/0.97      inference(global_propositional_subsumption,
% 2.47/0.97                [status(thm)],
% 2.47/0.97                [c_543,c_17]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_545,plain,
% 2.47/0.97      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1)
% 2.47/0.97      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.47/0.97      inference(renaming,[status(thm)],[c_544]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_603,plain,
% 2.47/0.97      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_enumset1(sK1,sK1,sK1) ),
% 2.47/0.97      inference(equality_resolution_simp,[status(thm)],[c_545]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_8,plain,
% 2.47/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.47/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.47/0.97      inference(cnf_transformation,[],[f41]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_367,plain,
% 2.47/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.47/0.97      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.47/0.97      | sK4 != X2 ),
% 2.47/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_368,plain,
% 2.47/0.97      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 2.47/0.97      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.47/0.97      inference(unflattening,[status(thm)],[c_367]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1029,plain,
% 2.47/0.97      ( k1_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4) = k1_relat_1(sK4) ),
% 2.47/0.97      inference(equality_resolution,[status(thm)],[c_368]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1100,plain,
% 2.47/0.97      ( k1_enumset1(sK1,sK1,sK1) = k1_relat_1(sK4) ),
% 2.47/0.97      inference(light_normalisation,[status(thm)],[c_603,c_1029]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_2,plain,
% 2.47/0.97      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 2.47/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_929,plain,
% 2.47/0.97      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) = iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1208,plain,
% 2.47/0.97      ( r2_hidden(sK1,k1_relat_1(sK4)) = iProver_top ),
% 2.47/0.97      inference(superposition,[status(thm)],[c_1100,c_929]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_6,plain,
% 2.47/0.97      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.47/0.97      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.47/0.97      | ~ v1_funct_1(X1)
% 2.47/0.97      | ~ v1_relat_1(X1)
% 2.47/0.97      | k1_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k1_enumset1(X2,X2,X0)) ),
% 2.47/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_20,negated_conjecture,
% 2.47/0.97      ( v1_funct_1(sK4) ),
% 2.47/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_251,plain,
% 2.47/0.97      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 2.47/0.97      | ~ r2_hidden(X2,k1_relat_1(X1))
% 2.47/0.97      | ~ v1_relat_1(X1)
% 2.47/0.97      | k1_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X0)) = k9_relat_1(X1,k1_enumset1(X2,X2,X0))
% 2.47/0.97      | sK4 != X1 ),
% 2.47/0.97      inference(resolution_lifted,[status(thm)],[c_6,c_20]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_252,plain,
% 2.47/0.97      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 2.47/0.97      | ~ r2_hidden(X1,k1_relat_1(sK4))
% 2.47/0.97      | ~ v1_relat_1(sK4)
% 2.47/0.97      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k1_enumset1(X0,X0,X1)) ),
% 2.47/0.97      inference(unflattening,[status(thm)],[c_251]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_924,plain,
% 2.47/0.97      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k1_enumset1(X0,X0,X1))
% 2.47/0.97      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.47/0.97      | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
% 2.47/0.97      | v1_relat_1(sK4) != iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_252]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_253,plain,
% 2.47/0.97      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k1_enumset1(X0,X0,X1))
% 2.47/0.97      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.47/0.97      | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
% 2.47/0.97      | v1_relat_1(sK4) != iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_252]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_724,plain,( X0 = X0 ),theory(equality) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1019,plain,
% 2.47/0.97      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.47/0.97      inference(instantiation,[status(thm)],[c_724]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_7,plain,
% 2.47/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.47/0.97      | v1_relat_1(X0) ),
% 2.47/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_376,plain,
% 2.47/0.97      ( v1_relat_1(X0)
% 2.47/0.97      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.47/0.97      | sK4 != X0 ),
% 2.47/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_377,plain,
% 2.47/0.97      ( v1_relat_1(sK4)
% 2.47/0.97      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.47/0.97      inference(unflattening,[status(thm)],[c_376]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1022,plain,
% 2.47/0.97      ( v1_relat_1(sK4)
% 2.47/0.97      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
% 2.47/0.97      inference(instantiation,[status(thm)],[c_377]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1023,plain,
% 2.47/0.97      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))
% 2.47/0.97      | v1_relat_1(sK4) = iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_1022]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1667,plain,
% 2.47/0.97      ( r2_hidden(X1,k1_relat_1(sK4)) != iProver_top
% 2.47/0.97      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.47/0.97      | k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k1_enumset1(X0,X0,X1)) ),
% 2.47/0.97      inference(global_propositional_subsumption,
% 2.47/0.97                [status(thm)],
% 2.47/0.97                [c_924,c_253,c_1019,c_1023]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1668,plain,
% 2.47/0.97      ( k1_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X1)) = k9_relat_1(sK4,k1_enumset1(X0,X0,X1))
% 2.47/0.97      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.47/0.97      | r2_hidden(X1,k1_relat_1(sK4)) != iProver_top ),
% 2.47/0.97      inference(renaming,[status(thm)],[c_1667]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1897,plain,
% 2.47/0.97      ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,X0)) = k9_relat_1(sK4,k1_enumset1(sK1,sK1,X0))
% 2.47/0.97      | r2_hidden(X0,k1_relat_1(sK4)) != iProver_top ),
% 2.47/0.97      inference(superposition,[status(thm)],[c_1208,c_1668]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_2314,plain,
% 2.47/0.97      ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k9_relat_1(sK4,k1_enumset1(sK1,sK1,sK1)) ),
% 2.47/0.97      inference(superposition,[status(thm)],[c_1208,c_1897]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_923,plain,
% 2.47/0.97      ( k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.47/0.97      | v1_relat_1(sK4) = iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1201,plain,
% 2.47/0.97      ( v1_relat_1(sK4) = iProver_top ),
% 2.47/0.97      inference(global_propositional_subsumption,
% 2.47/0.97                [status(thm)],
% 2.47/0.97                [c_923,c_1019,c_1023]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_5,plain,
% 2.47/0.97      ( ~ v1_relat_1(X0)
% 2.47/0.97      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.47/0.97      inference(cnf_transformation,[],[f38]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_926,plain,
% 2.47/0.97      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.47/0.97      | v1_relat_1(X0) != iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1277,plain,
% 2.47/0.97      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 2.47/0.97      inference(superposition,[status(thm)],[c_1201,c_926]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_2316,plain,
% 2.47/0.97      ( k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1)) = k2_relat_1(sK4) ),
% 2.47/0.97      inference(light_normalisation,[status(thm)],[c_2314,c_1100,c_1277]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_16,negated_conjecture,
% 2.47/0.97      ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) ),
% 2.47/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_925,plain,
% 2.47/0.97      ( r1_tarski(k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.47/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1105,plain,
% 2.47/0.97      ( r1_tarski(k7_relset_1(k1_relat_1(sK4),sK2,sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.47/0.97      inference(demodulation,[status(thm)],[c_1100,c_925]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_9,plain,
% 2.47/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.47/0.97      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.47/0.97      inference(cnf_transformation,[],[f42]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_358,plain,
% 2.47/0.97      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.47/0.97      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.47/0.97      | sK4 != X2 ),
% 2.47/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_18]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_359,plain,
% 2.47/0.97      ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
% 2.47/0.97      | k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.47/0.97      inference(unflattening,[status(thm)],[c_358]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1061,plain,
% 2.47/0.97      ( k7_relset_1(k1_enumset1(sK1,sK1,sK1),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 2.47/0.97      inference(equality_resolution,[status(thm)],[c_359]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1395,plain,
% 2.47/0.97      ( k7_relset_1(k1_relat_1(sK4),sK2,sK4,X0) = k9_relat_1(sK4,X0) ),
% 2.47/0.97      inference(light_normalisation,[status(thm)],[c_1061,c_1100]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_1521,plain,
% 2.47/0.97      ( r1_tarski(k9_relat_1(sK4,sK3),k1_enumset1(k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1),k1_funct_1(sK4,sK1))) != iProver_top ),
% 2.47/0.97      inference(demodulation,[status(thm)],[c_1105,c_1395]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_2408,plain,
% 2.47/0.97      ( r1_tarski(k9_relat_1(sK4,sK3),k2_relat_1(sK4)) != iProver_top ),
% 2.47/0.97      inference(demodulation,[status(thm)],[c_2316,c_1521]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(c_2424,plain,
% 2.47/0.97      ( v1_relat_1(sK4) != iProver_top ),
% 2.47/0.97      inference(superposition,[status(thm)],[c_927,c_2408]) ).
% 2.47/0.97  
% 2.47/0.97  cnf(contradiction,plain,
% 2.47/0.97      ( $false ),
% 2.47/0.97      inference(minisat,[status(thm)],[c_2424,c_1023,c_1019]) ).
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.47/0.97  
% 2.47/0.97  ------                               Statistics
% 2.47/0.97  
% 2.47/0.97  ------ General
% 2.47/0.97  
% 2.47/0.97  abstr_ref_over_cycles:                  0
% 2.47/0.97  abstr_ref_under_cycles:                 0
% 2.47/0.97  gc_basic_clause_elim:                   0
% 2.47/0.97  forced_gc_time:                         0
% 2.47/0.97  parsing_time:                           0.009
% 2.47/0.97  unif_index_cands_time:                  0.
% 2.47/0.97  unif_index_add_time:                    0.
% 2.47/0.97  orderings_time:                         0.
% 2.47/0.97  out_proof_time:                         0.01
% 2.47/0.97  total_time:                             0.127
% 2.47/0.97  num_of_symbols:                         52
% 2.47/0.97  num_of_terms:                           2695
% 2.47/0.97  
% 2.47/0.97  ------ Preprocessing
% 2.47/0.97  
% 2.47/0.97  num_of_splits:                          0
% 2.47/0.97  num_of_split_atoms:                     0
% 2.47/0.97  num_of_reused_defs:                     0
% 2.47/0.97  num_eq_ax_congr_red:                    14
% 2.47/0.97  num_of_sem_filtered_clauses:            1
% 2.47/0.97  num_of_subtypes:                        0
% 2.47/0.97  monotx_restored_types:                  0
% 2.47/0.97  sat_num_of_epr_types:                   0
% 2.47/0.97  sat_num_of_non_cyclic_types:            0
% 2.47/0.97  sat_guarded_non_collapsed_types:        0
% 2.47/0.97  num_pure_diseq_elim:                    0
% 2.47/0.97  simp_replaced_by:                       0
% 2.47/0.97  res_preprocessed:                       93
% 2.47/0.97  prep_upred:                             0
% 2.47/0.97  prep_unflattend:                        31
% 2.47/0.97  smt_new_axioms:                         0
% 2.47/0.97  pred_elim_cands:                        3
% 2.47/0.97  pred_elim:                              3
% 2.47/0.97  pred_elim_cl:                           6
% 2.47/0.97  pred_elim_cycles:                       9
% 2.47/0.97  merged_defs:                            0
% 2.47/0.97  merged_defs_ncl:                        0
% 2.47/0.97  bin_hyper_res:                          0
% 2.47/0.97  prep_cycles:                            4
% 2.47/0.97  pred_elim_time:                         0.008
% 2.47/0.97  splitting_time:                         0.
% 2.47/0.97  sem_filter_time:                        0.
% 2.47/0.97  monotx_time:                            0.
% 2.47/0.97  subtype_inf_time:                       0.
% 2.47/0.97  
% 2.47/0.97  ------ Problem properties
% 2.47/0.97  
% 2.47/0.97  clauses:                                15
% 2.47/0.97  conjectures:                            2
% 2.47/0.97  epr:                                    1
% 2.47/0.97  horn:                                   13
% 2.47/0.97  ground:                                 5
% 2.47/0.97  unary:                                  4
% 2.47/0.97  binary:                                 6
% 2.47/0.97  lits:                                   33
% 2.47/0.97  lits_eq:                                21
% 2.47/0.97  fd_pure:                                0
% 2.47/0.97  fd_pseudo:                              0
% 2.47/0.97  fd_cond:                                0
% 2.47/0.97  fd_pseudo_cond:                         2
% 2.47/0.97  ac_symbols:                             0
% 2.47/0.97  
% 2.47/0.97  ------ Propositional Solver
% 2.47/0.97  
% 2.47/0.97  prop_solver_calls:                      27
% 2.47/0.97  prop_fast_solver_calls:                 605
% 2.47/0.97  smt_solver_calls:                       0
% 2.47/0.97  smt_fast_solver_calls:                  0
% 2.47/0.97  prop_num_of_clauses:                    849
% 2.47/0.97  prop_preprocess_simplified:             3511
% 2.47/0.97  prop_fo_subsumed:                       7
% 2.47/0.97  prop_solver_time:                       0.
% 2.47/0.97  smt_solver_time:                        0.
% 2.47/0.97  smt_fast_solver_time:                   0.
% 2.47/0.97  prop_fast_solver_time:                  0.
% 2.47/0.97  prop_unsat_core_time:                   0.
% 2.47/0.97  
% 2.47/0.97  ------ QBF
% 2.47/0.97  
% 2.47/0.97  qbf_q_res:                              0
% 2.47/0.97  qbf_num_tautologies:                    0
% 2.47/0.97  qbf_prep_cycles:                        0
% 2.47/0.97  
% 2.47/0.97  ------ BMC1
% 2.47/0.97  
% 2.47/0.97  bmc1_current_bound:                     -1
% 2.47/0.97  bmc1_last_solved_bound:                 -1
% 2.47/0.97  bmc1_unsat_core_size:                   -1
% 2.47/0.97  bmc1_unsat_core_parents_size:           -1
% 2.47/0.97  bmc1_merge_next_fun:                    0
% 2.47/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.47/0.97  
% 2.47/0.97  ------ Instantiation
% 2.47/0.97  
% 2.47/0.97  inst_num_of_clauses:                    274
% 2.47/0.97  inst_num_in_passive:                    126
% 2.47/0.97  inst_num_in_active:                     135
% 2.47/0.97  inst_num_in_unprocessed:                13
% 2.47/0.97  inst_num_of_loops:                      150
% 2.47/0.97  inst_num_of_learning_restarts:          0
% 2.47/0.97  inst_num_moves_active_passive:          13
% 2.47/0.97  inst_lit_activity:                      0
% 2.47/0.97  inst_lit_activity_moves:                0
% 2.47/0.97  inst_num_tautologies:                   0
% 2.47/0.97  inst_num_prop_implied:                  0
% 2.47/0.97  inst_num_existing_simplified:           0
% 2.47/0.97  inst_num_eq_res_simplified:             0
% 2.47/0.97  inst_num_child_elim:                    0
% 2.47/0.97  inst_num_of_dismatching_blockings:      79
% 2.47/0.97  inst_num_of_non_proper_insts:           270
% 2.47/0.97  inst_num_of_duplicates:                 0
% 2.47/0.97  inst_inst_num_from_inst_to_res:         0
% 2.47/0.97  inst_dismatching_checking_time:         0.
% 2.47/0.97  
% 2.47/0.97  ------ Resolution
% 2.47/0.97  
% 2.47/0.97  res_num_of_clauses:                     0
% 2.47/0.97  res_num_in_passive:                     0
% 2.47/0.97  res_num_in_active:                      0
% 2.47/0.97  res_num_of_loops:                       97
% 2.47/0.97  res_forward_subset_subsumed:            44
% 2.47/0.97  res_backward_subset_subsumed:           0
% 2.47/0.97  res_forward_subsumed:                   0
% 2.47/0.97  res_backward_subsumed:                  0
% 2.47/0.97  res_forward_subsumption_resolution:     0
% 2.47/0.97  res_backward_subsumption_resolution:    0
% 2.47/0.97  res_clause_to_clause_subsumption:       58
% 2.47/0.97  res_orphan_elimination:                 0
% 2.47/0.97  res_tautology_del:                      20
% 2.47/0.97  res_num_eq_res_simplified:              1
% 2.47/0.97  res_num_sel_changes:                    0
% 2.47/0.97  res_moves_from_active_to_pass:          0
% 2.47/0.97  
% 2.47/0.97  ------ Superposition
% 2.47/0.97  
% 2.47/0.97  sup_time_total:                         0.
% 2.47/0.97  sup_time_generating:                    0.
% 2.47/0.97  sup_time_sim_full:                      0.
% 2.47/0.97  sup_time_sim_immed:                     0.
% 2.47/0.97  
% 2.47/0.97  sup_num_of_clauses:                     32
% 2.47/0.97  sup_num_in_active:                      24
% 2.47/0.97  sup_num_in_passive:                     8
% 2.47/0.97  sup_num_of_loops:                       29
% 2.47/0.97  sup_fw_superposition:                   11
% 2.47/0.97  sup_bw_superposition:                   6
% 2.47/0.97  sup_immediate_simplified:               1
% 2.47/0.97  sup_given_eliminated:                   0
% 2.47/0.97  comparisons_done:                       0
% 2.47/0.97  comparisons_avoided:                    11
% 2.47/0.97  
% 2.47/0.97  ------ Simplifications
% 2.47/0.97  
% 2.47/0.97  
% 2.47/0.97  sim_fw_subset_subsumed:                 0
% 2.47/0.97  sim_bw_subset_subsumed:                 0
% 2.47/0.97  sim_fw_subsumed:                        0
% 2.47/0.97  sim_bw_subsumed:                        0
% 2.47/0.97  sim_fw_subsumption_res:                 0
% 2.47/0.97  sim_bw_subsumption_res:                 0
% 2.47/0.97  sim_tautology_del:                      0
% 2.47/0.97  sim_eq_tautology_del:                   2
% 2.47/0.97  sim_eq_res_simp:                        0
% 2.47/0.97  sim_fw_demodulated:                     1
% 2.47/0.97  sim_bw_demodulated:                     6
% 2.47/0.97  sim_light_normalised:                   3
% 2.47/0.97  sim_joinable_taut:                      0
% 2.47/0.97  sim_joinable_simp:                      0
% 2.47/0.97  sim_ac_normalised:                      0
% 2.47/0.97  sim_smt_subsumption:                    0
% 2.47/0.97  
%------------------------------------------------------------------------------
