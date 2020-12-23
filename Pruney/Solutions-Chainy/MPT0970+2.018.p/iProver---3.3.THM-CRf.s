%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:49 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 304 expanded)
%              Number of clauses        :   82 ( 115 expanded)
%              Number of leaves         :   18 (  73 expanded)
%              Depth                    :   17
%              Number of atoms          :  406 (1291 expanded)
%              Number of equality atoms :  137 ( 362 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK5(X3)) = X3
        & r2_hidden(sK5(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK2,sK3,sK4) != sK3
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK4,X4) = X3
              & r2_hidden(X4,sK2) )
          | ~ r2_hidden(X3,sK3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k2_relset_1(sK2,sK3,sK4) != sK3
    & ! [X3] :
        ( ( k1_funct_1(sK4,sK5(X3)) = X3
          & r2_hidden(sK5(X3),sK2) )
        | ~ r2_hidden(X3,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f33,f32])).

fof(f52,plain,(
    ! [X3] :
      ( k1_funct_1(sK4,sK5(X3)) = X3
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X3] :
      ( r2_hidden(sK5(X3),sK2)
      | ~ r2_hidden(X3,sK3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_646,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_11635,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_646])).

cnf(c_11636,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_11635])).

cnf(c_645,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2021,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_646,c_645])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK4,sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_4700,plain,
    ( ~ r2_hidden(X0,sK3)
    | X0 = k1_funct_1(sK4,sK5(X0)) ),
    inference(resolution,[status(thm)],[c_2021,c_14])).

cnf(c_648,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2155,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_648,c_645])).

cnf(c_5083,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(k1_funct_1(sK4,sK5(X0)),X1) ),
    inference(resolution,[status(thm)],[c_4700,c_2155])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_211,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | sK4 != X0
    | sK3 != X2
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_212,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_211])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_216,plain,
    ( r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
    | ~ r2_hidden(X0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_212,c_18,c_16])).

cnf(c_217,plain,
    ( ~ r2_hidden(X0,sK2)
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
    | k1_xboole_0 = sK3 ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_5534,plain,
    ( r2_hidden(X0,k2_relset_1(sK2,sK3,sK4))
    | ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(sK5(X0),sK2)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[status(thm)],[c_5083,c_217])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK5(X0),sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8877,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(X0,k2_relset_1(sK2,sK3,sK4))
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5534,c_15])).

cnf(c_8878,plain,
    ( r2_hidden(X0,k2_relset_1(sK2,sK3,sK4))
    | ~ r2_hidden(X0,sK3)
    | k1_xboole_0 = sK3 ),
    inference(renaming,[status(thm)],[c_8877])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8897,plain,
    ( ~ r2_hidden(sK0(X0,k2_relset_1(sK2,sK3,sK4)),sK3)
    | r1_tarski(X0,k2_relset_1(sK2,sK3,sK4))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[status(thm)],[c_8878,c_0])).

cnf(c_8898,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(sK0(X0,k2_relset_1(sK2,sK3,sK4)),sK3) != iProver_top
    | r1_tarski(X0,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8897])).

cnf(c_8900,plain,
    ( k1_xboole_0 = sK3
    | r2_hidden(sK0(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) != iProver_top
    | r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_8898])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3435,plain,
    ( r2_hidden(sK0(sK3,k2_relset_1(sK2,sK3,sK4)),sK3)
    | r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3436,plain,
    ( r2_hidden(sK0(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) = iProver_top
    | r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3435])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3240,plain,
    ( r1_tarski(k1_xboole_0,sK1(sK3,k2_relset_1(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3243,plain,
    ( r1_tarski(k1_xboole_0,sK1(sK3,k2_relset_1(sK2,sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3240])).

cnf(c_647,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1424,plain,
    ( ~ r1_tarski(X0,sK1(sK3,k2_relset_1(sK2,sK3,sK4)))
    | r1_tarski(sK3,sK1(sK3,k2_relset_1(sK2,sK3,sK4)))
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_3239,plain,
    ( r1_tarski(sK3,sK1(sK3,k2_relset_1(sK2,sK3,sK4)))
    | ~ r1_tarski(k1_xboole_0,sK1(sK3,k2_relset_1(sK2,sK3,sK4)))
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1424])).

cnf(c_3241,plain,
    ( sK3 != k1_xboole_0
    | r1_tarski(sK3,sK1(sK3,k2_relset_1(sK2,sK3,sK4))) = iProver_top
    | r1_tarski(k1_xboole_0,sK1(sK3,k2_relset_1(sK2,sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3239])).

cnf(c_1147,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X1)
    | k2_relset_1(sK2,sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_1749,plain,
    ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
    | ~ r1_tarski(k2_relat_1(sK4),X0)
    | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_1750,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1749])).

cnf(c_1752,plain,
    ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) = iProver_top
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1750])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1198,plain,
    ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),X0)
    | ~ r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3)
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1470,plain,
    ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4))
    | ~ r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3)
    | ~ r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_1471,plain,
    ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) = iProver_top
    | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) != iProver_top
    | r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1470])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1208,plain,
    ( ~ r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4))
    | ~ r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3)
    | k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1209,plain,
    ( k2_relset_1(sK2,sK3,sK4) = sK3
    | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) != iProver_top
    | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1208])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1199,plain,
    ( ~ r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3)
    | ~ r1_tarski(sK3,sK1(sK3,k2_relset_1(sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1200,plain,
    ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) != iProver_top
    | r1_tarski(sK3,sK1(sK3,k2_relset_1(sK2,sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1199])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_245,plain,
    ( v5_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_16])).

cnf(c_246,plain,
    ( v5_relat_1(sK4,X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_257,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_258,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_277,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_258])).

cnf(c_278,plain,
    ( ~ v5_relat_1(sK4,X0)
    | r1_tarski(k2_relat_1(sK4),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_277])).

cnf(c_314,plain,
    ( r1_tarski(k2_relat_1(sK4),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_246,c_278])).

cnf(c_641,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_314])).

cnf(c_904,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_1161,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_904])).

cnf(c_642,plain,
    ( r1_tarski(k2_relat_1(sK4),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_314])).

cnf(c_1110,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3)
    | ~ sP1_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_642])).

cnf(c_1111,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1110])).

cnf(c_1087,plain,
    ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),X0)
    | ~ r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4))
    | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1091,plain,
    ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),X0) = iProver_top
    | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) != iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1087])).

cnf(c_1093,plain,
    ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) != iProver_top
    | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) = iProver_top
    | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1055,plain,
    ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4))
    | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3)
    | k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1056,plain,
    ( k2_relset_1(sK2,sK3,sK4) = sK3
    | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) = iProver_top
    | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1055])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_236,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_237,plain,
    ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_1024,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_1023,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_643,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_314])).

cnf(c_663,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_662,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_13,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11636,c_8900,c_3436,c_3243,c_3241,c_1752,c_1471,c_1209,c_1200,c_1161,c_1111,c_1093,c_1056,c_1024,c_1023,c_663,c_662,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.76/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.76/1.00  
% 3.76/1.00  ------  iProver source info
% 3.76/1.00  
% 3.76/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.76/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.76/1.00  git: non_committed_changes: false
% 3.76/1.00  git: last_make_outside_of_git: false
% 3.76/1.00  
% 3.76/1.00  ------ 
% 3.76/1.00  ------ Parsing...
% 3.76/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/1.00  
% 3.76/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.76/1.00  ------ Proving...
% 3.76/1.00  ------ Problem Properties 
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  clauses                                 15
% 3.76/1.00  conjectures                             3
% 3.76/1.00  EPR                                     4
% 3.76/1.00  Horn                                    11
% 3.76/1.00  unary                                   2
% 3.76/1.00  binary                                  8
% 3.76/1.00  lits                                    33
% 3.76/1.00  lits eq                                 9
% 3.76/1.00  fd_pure                                 0
% 3.76/1.00  fd_pseudo                               0
% 3.76/1.00  fd_cond                                 0
% 3.76/1.00  fd_pseudo_cond                          2
% 3.76/1.00  AC symbols                              0
% 3.76/1.00  
% 3.76/1.00  ------ Input Options Time Limit: Unbounded
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  ------ 
% 3.76/1.00  Current options:
% 3.76/1.00  ------ 
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  ------ Proving...
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  % SZS status Theorem for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  fof(f10,conjecture,(
% 3.76/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f11,negated_conjecture,(
% 3.76/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.76/1.00    inference(negated_conjecture,[],[f10])).
% 3.76/1.00  
% 3.76/1.00  fof(f22,plain,(
% 3.76/1.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.76/1.00    inference(ennf_transformation,[],[f11])).
% 3.76/1.00  
% 3.76/1.00  fof(f23,plain,(
% 3.76/1.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.76/1.00    inference(flattening,[],[f22])).
% 3.76/1.00  
% 3.76/1.00  fof(f33,plain,(
% 3.76/1.00    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK5(X3)) = X3 & r2_hidden(sK5(X3),X0)))) )),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f32,plain,(
% 3.76/1.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : (? [X4] : (k1_funct_1(sK4,X4) = X3 & r2_hidden(X4,sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f34,plain,(
% 3.76/1.00    k2_relset_1(sK2,sK3,sK4) != sK3 & ! [X3] : ((k1_funct_1(sK4,sK5(X3)) = X3 & r2_hidden(sK5(X3),sK2)) | ~r2_hidden(X3,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f23,f33,f32])).
% 3.76/1.00  
% 3.76/1.00  fof(f52,plain,(
% 3.76/1.00    ( ! [X3] : (k1_funct_1(sK4,sK5(X3)) = X3 | ~r2_hidden(X3,sK3)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f34])).
% 3.76/1.00  
% 3.76/1.00  fof(f9,axiom,(
% 3.76/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f20,plain,(
% 3.76/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.76/1.00    inference(ennf_transformation,[],[f9])).
% 3.76/1.00  
% 3.76/1.00  fof(f21,plain,(
% 3.76/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.76/1.00    inference(flattening,[],[f20])).
% 3.76/1.00  
% 3.76/1.00  fof(f47,plain,(
% 3.76/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f21])).
% 3.76/1.00  
% 3.76/1.00  fof(f49,plain,(
% 3.76/1.00    v1_funct_2(sK4,sK2,sK3)),
% 3.76/1.00    inference(cnf_transformation,[],[f34])).
% 3.76/1.00  
% 3.76/1.00  fof(f48,plain,(
% 3.76/1.00    v1_funct_1(sK4)),
% 3.76/1.00    inference(cnf_transformation,[],[f34])).
% 3.76/1.00  
% 3.76/1.00  fof(f50,plain,(
% 3.76/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.76/1.00    inference(cnf_transformation,[],[f34])).
% 3.76/1.00  
% 3.76/1.00  fof(f51,plain,(
% 3.76/1.00    ( ! [X3] : (r2_hidden(sK5(X3),sK2) | ~r2_hidden(X3,sK3)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f34])).
% 3.76/1.00  
% 3.76/1.00  fof(f1,axiom,(
% 3.76/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f13,plain,(
% 3.76/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.76/1.00    inference(ennf_transformation,[],[f1])).
% 3.76/1.00  
% 3.76/1.00  fof(f24,plain,(
% 3.76/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.76/1.00    inference(nnf_transformation,[],[f13])).
% 3.76/1.00  
% 3.76/1.00  fof(f25,plain,(
% 3.76/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.76/1.00    inference(rectify,[],[f24])).
% 3.76/1.00  
% 3.76/1.00  fof(f26,plain,(
% 3.76/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f27,plain,(
% 3.76/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.76/1.00  
% 3.76/1.00  fof(f37,plain,(
% 3.76/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f27])).
% 3.76/1.00  
% 3.76/1.00  fof(f36,plain,(
% 3.76/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f27])).
% 3.76/1.00  
% 3.76/1.00  fof(f3,axiom,(
% 3.76/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f40,plain,(
% 3.76/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f3])).
% 3.76/1.00  
% 3.76/1.00  fof(f35,plain,(
% 3.76/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f27])).
% 3.76/1.00  
% 3.76/1.00  fof(f2,axiom,(
% 3.76/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f14,plain,(
% 3.76/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.76/1.00    inference(ennf_transformation,[],[f2])).
% 3.76/1.00  
% 3.76/1.00  fof(f28,plain,(
% 3.76/1.00    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.76/1.00    inference(nnf_transformation,[],[f14])).
% 3.76/1.00  
% 3.76/1.00  fof(f29,plain,(
% 3.76/1.00    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.76/1.00    introduced(choice_axiom,[])).
% 3.76/1.00  
% 3.76/1.00  fof(f30,plain,(
% 3.76/1.00    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 3.76/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 3.76/1.00  
% 3.76/1.00  fof(f39,plain,(
% 3.76/1.00    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f30])).
% 3.76/1.00  
% 3.76/1.00  fof(f5,axiom,(
% 3.76/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f16,plain,(
% 3.76/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.76/1.00    inference(ennf_transformation,[],[f5])).
% 3.76/1.00  
% 3.76/1.00  fof(f43,plain,(
% 3.76/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f16])).
% 3.76/1.00  
% 3.76/1.00  fof(f7,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f12,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.76/1.00    inference(pure_predicate_removal,[],[f7])).
% 3.76/1.00  
% 3.76/1.00  fof(f18,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/1.00    inference(ennf_transformation,[],[f12])).
% 3.76/1.00  
% 3.76/1.00  fof(f45,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f18])).
% 3.76/1.00  
% 3.76/1.00  fof(f4,axiom,(
% 3.76/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f15,plain,(
% 3.76/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.76/1.00    inference(ennf_transformation,[],[f4])).
% 3.76/1.00  
% 3.76/1.00  fof(f31,plain,(
% 3.76/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.76/1.00    inference(nnf_transformation,[],[f15])).
% 3.76/1.00  
% 3.76/1.00  fof(f41,plain,(
% 3.76/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f31])).
% 3.76/1.00  
% 3.76/1.00  fof(f6,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f17,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/1.00    inference(ennf_transformation,[],[f6])).
% 3.76/1.00  
% 3.76/1.00  fof(f44,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f17])).
% 3.76/1.00  
% 3.76/1.00  fof(f38,plain,(
% 3.76/1.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.76/1.00    inference(cnf_transformation,[],[f30])).
% 3.76/1.00  
% 3.76/1.00  fof(f8,axiom,(
% 3.76/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.76/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/1.00  
% 3.76/1.00  fof(f19,plain,(
% 3.76/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/1.00    inference(ennf_transformation,[],[f8])).
% 3.76/1.00  
% 3.76/1.00  fof(f46,plain,(
% 3.76/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/1.00    inference(cnf_transformation,[],[f19])).
% 3.76/1.00  
% 3.76/1.00  fof(f53,plain,(
% 3.76/1.00    k2_relset_1(sK2,sK3,sK4) != sK3),
% 3.76/1.00    inference(cnf_transformation,[],[f34])).
% 3.76/1.00  
% 3.76/1.00  cnf(c_646,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11635,plain,
% 3.76/1.00      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_646]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11636,plain,
% 3.76/1.00      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_11635]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_645,plain,( X0 = X0 ),theory(equality) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2021,plain,
% 3.76/1.00      ( X0 != X1 | X1 = X0 ),
% 3.76/1.00      inference(resolution,[status(thm)],[c_646,c_645]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_14,negated_conjecture,
% 3.76/1.00      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK4,sK5(X0)) = X0 ),
% 3.76/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4700,plain,
% 3.76/1.00      ( ~ r2_hidden(X0,sK3) | X0 = k1_funct_1(sK4,sK5(X0)) ),
% 3.76/1.00      inference(resolution,[status(thm)],[c_2021,c_14]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_648,plain,
% 3.76/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.76/1.00      theory(equality) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2155,plain,
% 3.76/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 3.76/1.00      inference(resolution,[status(thm)],[c_648,c_645]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5083,plain,
% 3.76/1.00      ( r2_hidden(X0,X1)
% 3.76/1.00      | ~ r2_hidden(X0,sK3)
% 3.76/1.00      | ~ r2_hidden(k1_funct_1(sK4,sK5(X0)),X1) ),
% 3.76/1.00      inference(resolution,[status(thm)],[c_4700,c_2155]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_12,plain,
% 3.76/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.76/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | ~ r2_hidden(X3,X1)
% 3.76/1.00      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.76/1.00      | ~ v1_funct_1(X0)
% 3.76/1.00      | k1_xboole_0 = X2 ),
% 3.76/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_17,negated_conjecture,
% 3.76/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.76/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_211,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | ~ r2_hidden(X3,X1)
% 3.76/1.00      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.76/1.00      | ~ v1_funct_1(X0)
% 3.76/1.00      | sK4 != X0
% 3.76/1.00      | sK3 != X2
% 3.76/1.00      | sK2 != X1
% 3.76/1.00      | k1_xboole_0 = X2 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_212,plain,
% 3.76/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.76/1.00      | ~ r2_hidden(X0,sK2)
% 3.76/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
% 3.76/1.00      | ~ v1_funct_1(sK4)
% 3.76/1.00      | k1_xboole_0 = sK3 ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_211]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_18,negated_conjecture,
% 3.76/1.00      ( v1_funct_1(sK4) ),
% 3.76/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_16,negated_conjecture,
% 3.76/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.76/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_216,plain,
% 3.76/1.00      ( r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
% 3.76/1.00      | ~ r2_hidden(X0,sK2)
% 3.76/1.00      | k1_xboole_0 = sK3 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_212,c_18,c_16]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_217,plain,
% 3.76/1.00      ( ~ r2_hidden(X0,sK2)
% 3.76/1.00      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK2,sK3,sK4))
% 3.76/1.00      | k1_xboole_0 = sK3 ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_216]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5534,plain,
% 3.76/1.00      ( r2_hidden(X0,k2_relset_1(sK2,sK3,sK4))
% 3.76/1.00      | ~ r2_hidden(X0,sK3)
% 3.76/1.00      | ~ r2_hidden(sK5(X0),sK2)
% 3.76/1.00      | k1_xboole_0 = sK3 ),
% 3.76/1.00      inference(resolution,[status(thm)],[c_5083,c_217]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_15,negated_conjecture,
% 3.76/1.00      ( ~ r2_hidden(X0,sK3) | r2_hidden(sK5(X0),sK2) ),
% 3.76/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8877,plain,
% 3.76/1.00      ( ~ r2_hidden(X0,sK3)
% 3.76/1.00      | r2_hidden(X0,k2_relset_1(sK2,sK3,sK4))
% 3.76/1.00      | k1_xboole_0 = sK3 ),
% 3.76/1.00      inference(global_propositional_subsumption,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_5534,c_15]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8878,plain,
% 3.76/1.00      ( r2_hidden(X0,k2_relset_1(sK2,sK3,sK4))
% 3.76/1.00      | ~ r2_hidden(X0,sK3)
% 3.76/1.00      | k1_xboole_0 = sK3 ),
% 3.76/1.00      inference(renaming,[status(thm)],[c_8877]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_0,plain,
% 3.76/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8897,plain,
% 3.76/1.00      ( ~ r2_hidden(sK0(X0,k2_relset_1(sK2,sK3,sK4)),sK3)
% 3.76/1.00      | r1_tarski(X0,k2_relset_1(sK2,sK3,sK4))
% 3.76/1.00      | k1_xboole_0 = sK3 ),
% 3.76/1.00      inference(resolution,[status(thm)],[c_8878,c_0]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8898,plain,
% 3.76/1.00      ( k1_xboole_0 = sK3
% 3.76/1.00      | r2_hidden(sK0(X0,k2_relset_1(sK2,sK3,sK4)),sK3) != iProver_top
% 3.76/1.00      | r1_tarski(X0,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_8897]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8900,plain,
% 3.76/1.00      ( k1_xboole_0 = sK3
% 3.76/1.00      | r2_hidden(sK0(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) != iProver_top
% 3.76/1.00      | r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_8898]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1,plain,
% 3.76/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.76/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3435,plain,
% 3.76/1.00      ( r2_hidden(sK0(sK3,k2_relset_1(sK2,sK3,sK4)),sK3)
% 3.76/1.00      | r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3436,plain,
% 3.76/1.00      ( r2_hidden(sK0(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) = iProver_top
% 3.76/1.00      | r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_3435]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_5,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3240,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,sK1(sK3,k2_relset_1(sK2,sK3,sK4))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3243,plain,
% 3.76/1.00      ( r1_tarski(k1_xboole_0,sK1(sK3,k2_relset_1(sK2,sK3,sK4))) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_3240]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_647,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.76/1.00      theory(equality) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1424,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,sK1(sK3,k2_relset_1(sK2,sK3,sK4)))
% 3.76/1.00      | r1_tarski(sK3,sK1(sK3,k2_relset_1(sK2,sK3,sK4)))
% 3.76/1.00      | sK3 != X0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_647]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3239,plain,
% 3.76/1.00      ( r1_tarski(sK3,sK1(sK3,k2_relset_1(sK2,sK3,sK4)))
% 3.76/1.00      | ~ r1_tarski(k1_xboole_0,sK1(sK3,k2_relset_1(sK2,sK3,sK4)))
% 3.76/1.00      | sK3 != k1_xboole_0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1424]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3241,plain,
% 3.76/1.00      ( sK3 != k1_xboole_0
% 3.76/1.00      | r1_tarski(sK3,sK1(sK3,k2_relset_1(sK2,sK3,sK4))) = iProver_top
% 3.76/1.00      | r1_tarski(k1_xboole_0,sK1(sK3,k2_relset_1(sK2,sK3,sK4))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_3239]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1147,plain,
% 3.76/1.00      ( ~ r1_tarski(X0,X1)
% 3.76/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X1)
% 3.76/1.00      | k2_relset_1(sK2,sK3,sK4) != X0 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_647]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1749,plain,
% 3.76/1.00      ( r1_tarski(k2_relset_1(sK2,sK3,sK4),X0)
% 3.76/1.00      | ~ r1_tarski(k2_relat_1(sK4),X0)
% 3.76/1.00      | k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1147]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1750,plain,
% 3.76/1.00      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.76/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) = iProver_top
% 3.76/1.00      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_1749]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1752,plain,
% 3.76/1.00      ( k2_relset_1(sK2,sK3,sK4) != k2_relat_1(sK4)
% 3.76/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) = iProver_top
% 3.76/1.00      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1750]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_2,plain,
% 3.76/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.76/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1198,plain,
% 3.76/1.00      ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),X0)
% 3.76/1.00      | ~ r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3)
% 3.76/1.00      | ~ r1_tarski(sK3,X0) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1470,plain,
% 3.76/1.00      ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4))
% 3.76/1.00      | ~ r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3)
% 3.76/1.00      | ~ r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1198]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1471,plain,
% 3.76/1.00      ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) = iProver_top
% 3.76/1.00      | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) != iProver_top
% 3.76/1.00      | r1_tarski(sK3,k2_relset_1(sK2,sK3,sK4)) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_1470]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_3,plain,
% 3.76/1.00      ( ~ r2_hidden(sK1(X0,X1),X1)
% 3.76/1.00      | ~ r2_hidden(sK1(X0,X1),X0)
% 3.76/1.00      | X1 = X0 ),
% 3.76/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1208,plain,
% 3.76/1.00      ( ~ r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4))
% 3.76/1.00      | ~ r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3)
% 3.76/1.00      | k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1209,plain,
% 3.76/1.00      ( k2_relset_1(sK2,sK3,sK4) = sK3
% 3.76/1.00      | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) != iProver_top
% 3.76/1.00      | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_1208]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_8,plain,
% 3.76/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1199,plain,
% 3.76/1.00      ( ~ r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3)
% 3.76/1.00      | ~ r1_tarski(sK3,sK1(sK3,k2_relset_1(sK2,sK3,sK4))) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1200,plain,
% 3.76/1.00      ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) != iProver_top
% 3.76/1.00      | r1_tarski(sK3,sK1(sK3,k2_relset_1(sK2,sK3,sK4))) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_1199]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_10,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | v5_relat_1(X0,X2) ),
% 3.76/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_245,plain,
% 3.76/1.00      ( v5_relat_1(X0,X1)
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.76/1.00      | sK4 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_16]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_246,plain,
% 3.76/1.00      ( v5_relat_1(sK4,X0)
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_245]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_7,plain,
% 3.76/1.00      ( ~ v5_relat_1(X0,X1)
% 3.76/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.76/1.00      | ~ v1_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_9,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | v1_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_257,plain,
% 3.76/1.00      ( v1_relat_1(X0)
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.76/1.00      | sK4 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_258,plain,
% 3.76/1.00      ( v1_relat_1(sK4)
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_257]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_277,plain,
% 3.76/1.00      ( ~ v5_relat_1(X0,X1)
% 3.76/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.76/1.00      | sK4 != X0 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_258]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_278,plain,
% 3.76/1.00      ( ~ v5_relat_1(sK4,X0)
% 3.76/1.00      | r1_tarski(k2_relat_1(sK4),X0)
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_277]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_314,plain,
% 3.76/1.00      ( r1_tarski(k2_relat_1(sK4),X0)
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.76/1.00      inference(resolution,[status(thm)],[c_246,c_278]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_641,plain,
% 3.76/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.76/1.00      | ~ sP0_iProver_split ),
% 3.76/1.00      inference(splitting,
% 3.76/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.76/1.00                [c_314]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_904,plain,
% 3.76/1.00      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.76/1.00      | sP0_iProver_split != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1161,plain,
% 3.76/1.00      ( sP0_iProver_split != iProver_top ),
% 3.76/1.00      inference(equality_resolution,[status(thm)],[c_904]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_642,plain,
% 3.76/1.00      ( r1_tarski(k2_relat_1(sK4),X0)
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.76/1.00      | ~ sP1_iProver_split ),
% 3.76/1.00      inference(splitting,
% 3.76/1.00                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.76/1.00                [c_314]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1110,plain,
% 3.76/1.00      ( r1_tarski(k2_relat_1(sK4),sK3)
% 3.76/1.00      | ~ sP1_iProver_split
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_642]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1111,plain,
% 3.76/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.76/1.00      | r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
% 3.76/1.00      | sP1_iProver_split != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_1110]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1087,plain,
% 3.76/1.00      ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),X0)
% 3.76/1.00      | ~ r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4))
% 3.76/1.00      | ~ r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1091,plain,
% 3.76/1.00      ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),X0) = iProver_top
% 3.76/1.00      | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) != iProver_top
% 3.76/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),X0) != iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_1087]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1093,plain,
% 3.76/1.00      ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) != iProver_top
% 3.76/1.00      | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) = iProver_top
% 3.76/1.00      | r1_tarski(k2_relset_1(sK2,sK3,sK4),sK3) != iProver_top ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_1091]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_4,plain,
% 3.76/1.00      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 3.76/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1055,plain,
% 3.76/1.00      ( r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4))
% 3.76/1.00      | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3)
% 3.76/1.00      | k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1056,plain,
% 3.76/1.00      ( k2_relset_1(sK2,sK3,sK4) = sK3
% 3.76/1.00      | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),k2_relset_1(sK2,sK3,sK4)) = iProver_top
% 3.76/1.00      | r2_hidden(sK1(sK3,k2_relset_1(sK2,sK3,sK4)),sK3) = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_1055]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_11,plain,
% 3.76/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.76/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_236,plain,
% 3.76/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))
% 3.76/1.00      | sK4 != X2 ),
% 3.76/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_237,plain,
% 3.76/1.00      ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.76/1.00      inference(unflattening,[status(thm)],[c_236]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1024,plain,
% 3.76/1.00      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4)
% 3.76/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_237]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_1023,plain,
% 3.76/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_645]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_643,plain,
% 3.76/1.00      ( sP1_iProver_split | sP0_iProver_split ),
% 3.76/1.00      inference(splitting,
% 3.76/1.00                [splitting(split),new_symbols(definition,[])],
% 3.76/1.00                [c_314]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_663,plain,
% 3.76/1.00      ( sP1_iProver_split = iProver_top
% 3.76/1.00      | sP0_iProver_split = iProver_top ),
% 3.76/1.00      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_662,plain,
% 3.76/1.00      ( sK3 = sK3 ),
% 3.76/1.00      inference(instantiation,[status(thm)],[c_645]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(c_13,negated_conjecture,
% 3.76/1.00      ( k2_relset_1(sK2,sK3,sK4) != sK3 ),
% 3.76/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.76/1.00  
% 3.76/1.00  cnf(contradiction,plain,
% 3.76/1.00      ( $false ),
% 3.76/1.00      inference(minisat,
% 3.76/1.00                [status(thm)],
% 3.76/1.00                [c_11636,c_8900,c_3436,c_3243,c_3241,c_1752,c_1471,
% 3.76/1.00                 c_1209,c_1200,c_1161,c_1111,c_1093,c_1056,c_1024,c_1023,
% 3.76/1.00                 c_663,c_662,c_13]) ).
% 3.76/1.00  
% 3.76/1.00  
% 3.76/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/1.00  
% 3.76/1.00  ------                               Statistics
% 3.76/1.00  
% 3.76/1.00  ------ Selected
% 3.76/1.00  
% 3.76/1.00  total_time:                             0.374
% 3.76/1.00  
%------------------------------------------------------------------------------
