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
% DateTime   : Thu Dec  3 12:10:02 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 279 expanded)
%              Number of clauses        :   57 (  96 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   21
%              Number of atoms          :  309 (1029 expanded)
%              Number of equality atoms :   93 ( 230 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK4,X4) != sK1
          | ~ m1_subset_1(X4,sK2) )
      & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ! [X4] :
        ( k1_funct_1(sK4,X4) != sK1
        | ~ m1_subset_1(X4,sK2) )
    & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f34])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) != sK1
      | ~ m1_subset_1(X4,sK2) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1053,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1047,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_163,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_279,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_4])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_283,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_14,c_13,c_4])).

cnf(c_284,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(renaming,[status(thm)],[c_283])).

cnf(c_301,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X3 != X1
    | k1_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_163,c_284])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_1046,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_302])).

cnf(c_1361,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1046])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1057,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1472,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | m1_subset_1(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_1057])).

cnf(c_1621,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | m1_subset_1(sK0(X0,X1,sK4),sK2) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_1472])).

cnf(c_21,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1167,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1168,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1167])).

cnf(c_1675,plain,
    ( m1_subset_1(sK0(X0,X1,sK4),sK2) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1621,c_21,c_1168])).

cnf(c_1676,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | m1_subset_1(sK0(X0,X1,sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_1675])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1050,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1366,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1047,c_1050])).

cnf(c_17,negated_conjecture,
    ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1048,plain,
    ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1477,plain,
    ( r2_hidden(sK1,k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1366,c_1048])).

cnf(c_1051,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1259,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1051])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1052,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1456,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1259,c_1052])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1054,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_316,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_317,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_1045,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_318,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_1189,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | k1_funct_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1045,c_21,c_318,c_1168])).

cnf(c_1190,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_1189])).

cnf(c_1688,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_1190])).

cnf(c_1806,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1688,c_21,c_1168])).

cnf(c_1807,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1806])).

cnf(c_1816,plain,
    ( k1_funct_1(sK4,sK0(X0,k1_relat_1(sK4),sK4)) = X0
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1456,c_1807])).

cnf(c_2003,plain,
    ( k1_funct_1(sK4,sK0(sK1,k1_relat_1(sK4),sK4)) = sK1 ),
    inference(superposition,[status(thm)],[c_1477,c_1816])).

cnf(c_16,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | k1_funct_1(sK4,X0) != sK1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1049,plain,
    ( k1_funct_1(sK4,X0) != sK1
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2036,plain,
    ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2003,c_1049])).

cnf(c_2136,plain,
    ( r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1676,c_2036])).

cnf(c_2138,plain,
    ( r2_hidden(sK1,k2_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2136,c_1456])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2138,c_1477])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.31  % Computer   : n021.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % WCLimit    : 600
% 0.13/0.31  % DateTime   : Tue Dec  1 15:14:19 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.32  % Running in FOF mode
% 1.86/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/0.98  
% 1.86/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.86/0.98  
% 1.86/0.98  ------  iProver source info
% 1.86/0.98  
% 1.86/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.86/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.86/0.98  git: non_committed_changes: false
% 1.86/0.98  git: last_make_outside_of_git: false
% 1.86/0.98  
% 1.86/0.98  ------ 
% 1.86/0.98  
% 1.86/0.98  ------ Input Options
% 1.86/0.98  
% 1.86/0.98  --out_options                           all
% 1.86/0.98  --tptp_safe_out                         true
% 1.86/0.98  --problem_path                          ""
% 1.86/0.98  --include_path                          ""
% 1.86/0.98  --clausifier                            res/vclausify_rel
% 1.86/0.98  --clausifier_options                    --mode clausify
% 1.86/0.98  --stdin                                 false
% 1.86/0.98  --stats_out                             all
% 1.86/0.98  
% 1.86/0.98  ------ General Options
% 1.86/0.98  
% 1.86/0.98  --fof                                   false
% 1.86/0.98  --time_out_real                         305.
% 1.86/0.98  --time_out_virtual                      -1.
% 1.86/0.98  --symbol_type_check                     false
% 1.86/0.98  --clausify_out                          false
% 1.86/0.98  --sig_cnt_out                           false
% 1.86/0.98  --trig_cnt_out                          false
% 1.86/0.98  --trig_cnt_out_tolerance                1.
% 1.86/0.98  --trig_cnt_out_sk_spl                   false
% 1.86/0.98  --abstr_cl_out                          false
% 1.86/0.98  
% 1.86/0.98  ------ Global Options
% 1.86/0.98  
% 1.86/0.98  --schedule                              default
% 1.86/0.98  --add_important_lit                     false
% 1.86/0.98  --prop_solver_per_cl                    1000
% 1.86/0.98  --min_unsat_core                        false
% 1.86/0.98  --soft_assumptions                      false
% 1.86/0.98  --soft_lemma_size                       3
% 1.86/0.98  --prop_impl_unit_size                   0
% 1.86/0.98  --prop_impl_unit                        []
% 1.86/0.98  --share_sel_clauses                     true
% 1.86/0.98  --reset_solvers                         false
% 1.86/0.98  --bc_imp_inh                            [conj_cone]
% 1.86/0.98  --conj_cone_tolerance                   3.
% 1.86/0.98  --extra_neg_conj                        none
% 1.86/0.98  --large_theory_mode                     true
% 1.86/0.98  --prolific_symb_bound                   200
% 1.86/0.98  --lt_threshold                          2000
% 1.86/0.98  --clause_weak_htbl                      true
% 1.86/0.98  --gc_record_bc_elim                     false
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing Options
% 1.86/0.98  
% 1.86/0.98  --preprocessing_flag                    true
% 1.86/0.98  --time_out_prep_mult                    0.1
% 1.86/0.98  --splitting_mode                        input
% 1.86/0.98  --splitting_grd                         true
% 1.86/0.98  --splitting_cvd                         false
% 1.86/0.98  --splitting_cvd_svl                     false
% 1.86/0.98  --splitting_nvd                         32
% 1.86/0.98  --sub_typing                            true
% 1.86/0.98  --prep_gs_sim                           true
% 1.86/0.98  --prep_unflatten                        true
% 1.86/0.98  --prep_res_sim                          true
% 1.86/0.98  --prep_upred                            true
% 1.86/0.98  --prep_sem_filter                       exhaustive
% 1.86/0.98  --prep_sem_filter_out                   false
% 1.86/0.98  --pred_elim                             true
% 1.86/0.98  --res_sim_input                         true
% 1.86/0.98  --eq_ax_congr_red                       true
% 1.86/0.98  --pure_diseq_elim                       true
% 1.86/0.98  --brand_transform                       false
% 1.86/0.98  --non_eq_to_eq                          false
% 1.86/0.98  --prep_def_merge                        true
% 1.86/0.98  --prep_def_merge_prop_impl              false
% 1.86/0.98  --prep_def_merge_mbd                    true
% 1.86/0.98  --prep_def_merge_tr_red                 false
% 1.86/0.98  --prep_def_merge_tr_cl                  false
% 1.86/0.98  --smt_preprocessing                     true
% 1.86/0.98  --smt_ac_axioms                         fast
% 1.86/0.98  --preprocessed_out                      false
% 1.86/0.98  --preprocessed_stats                    false
% 1.86/0.98  
% 1.86/0.98  ------ Abstraction refinement Options
% 1.86/0.98  
% 1.86/0.98  --abstr_ref                             []
% 1.86/0.98  --abstr_ref_prep                        false
% 1.86/0.98  --abstr_ref_until_sat                   false
% 1.86/0.98  --abstr_ref_sig_restrict                funpre
% 1.86/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.86/0.98  --abstr_ref_under                       []
% 1.86/0.98  
% 1.86/0.98  ------ SAT Options
% 1.86/0.98  
% 1.86/0.98  --sat_mode                              false
% 1.86/0.98  --sat_fm_restart_options                ""
% 1.86/0.98  --sat_gr_def                            false
% 1.86/0.98  --sat_epr_types                         true
% 1.86/0.98  --sat_non_cyclic_types                  false
% 1.86/0.98  --sat_finite_models                     false
% 1.86/0.98  --sat_fm_lemmas                         false
% 1.86/0.98  --sat_fm_prep                           false
% 1.86/0.98  --sat_fm_uc_incr                        true
% 1.86/0.98  --sat_out_model                         small
% 1.86/0.98  --sat_out_clauses                       false
% 1.86/0.98  
% 1.86/0.98  ------ QBF Options
% 1.86/0.98  
% 1.86/0.98  --qbf_mode                              false
% 1.86/0.98  --qbf_elim_univ                         false
% 1.86/0.98  --qbf_dom_inst                          none
% 1.86/0.98  --qbf_dom_pre_inst                      false
% 1.86/0.98  --qbf_sk_in                             false
% 1.86/0.98  --qbf_pred_elim                         true
% 1.86/0.98  --qbf_split                             512
% 1.86/0.98  
% 1.86/0.98  ------ BMC1 Options
% 1.86/0.98  
% 1.86/0.98  --bmc1_incremental                      false
% 1.86/0.98  --bmc1_axioms                           reachable_all
% 1.86/0.98  --bmc1_min_bound                        0
% 1.86/0.98  --bmc1_max_bound                        -1
% 1.86/0.98  --bmc1_max_bound_default                -1
% 1.86/0.98  --bmc1_symbol_reachability              true
% 1.86/0.98  --bmc1_property_lemmas                  false
% 1.86/0.98  --bmc1_k_induction                      false
% 1.86/0.98  --bmc1_non_equiv_states                 false
% 1.86/0.98  --bmc1_deadlock                         false
% 1.86/0.98  --bmc1_ucm                              false
% 1.86/0.98  --bmc1_add_unsat_core                   none
% 1.86/0.98  --bmc1_unsat_core_children              false
% 1.86/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.86/0.98  --bmc1_out_stat                         full
% 1.86/0.98  --bmc1_ground_init                      false
% 1.86/0.98  --bmc1_pre_inst_next_state              false
% 1.86/0.98  --bmc1_pre_inst_state                   false
% 1.86/0.98  --bmc1_pre_inst_reach_state             false
% 1.86/0.98  --bmc1_out_unsat_core                   false
% 1.86/0.98  --bmc1_aig_witness_out                  false
% 1.86/0.98  --bmc1_verbose                          false
% 1.86/0.98  --bmc1_dump_clauses_tptp                false
% 1.86/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.86/0.98  --bmc1_dump_file                        -
% 1.86/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.86/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.86/0.98  --bmc1_ucm_extend_mode                  1
% 1.86/0.98  --bmc1_ucm_init_mode                    2
% 1.86/0.98  --bmc1_ucm_cone_mode                    none
% 1.86/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.86/0.98  --bmc1_ucm_relax_model                  4
% 1.86/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.86/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.86/0.98  --bmc1_ucm_layered_model                none
% 1.86/0.98  --bmc1_ucm_max_lemma_size               10
% 1.86/0.98  
% 1.86/0.98  ------ AIG Options
% 1.86/0.98  
% 1.86/0.98  --aig_mode                              false
% 1.86/0.98  
% 1.86/0.98  ------ Instantiation Options
% 1.86/0.98  
% 1.86/0.98  --instantiation_flag                    true
% 1.86/0.98  --inst_sos_flag                         false
% 1.86/0.98  --inst_sos_phase                        true
% 1.86/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.86/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.86/0.98  --inst_lit_sel_side                     num_symb
% 1.86/0.98  --inst_solver_per_active                1400
% 1.86/0.98  --inst_solver_calls_frac                1.
% 1.86/0.98  --inst_passive_queue_type               priority_queues
% 1.86/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.86/0.98  --inst_passive_queues_freq              [25;2]
% 1.86/0.98  --inst_dismatching                      true
% 1.86/0.98  --inst_eager_unprocessed_to_passive     true
% 1.86/0.98  --inst_prop_sim_given                   true
% 1.86/0.98  --inst_prop_sim_new                     false
% 1.86/0.98  --inst_subs_new                         false
% 1.86/0.98  --inst_eq_res_simp                      false
% 1.86/0.98  --inst_subs_given                       false
% 1.86/0.98  --inst_orphan_elimination               true
% 1.86/0.98  --inst_learning_loop_flag               true
% 1.86/0.98  --inst_learning_start                   3000
% 1.86/0.98  --inst_learning_factor                  2
% 1.86/0.98  --inst_start_prop_sim_after_learn       3
% 1.86/0.98  --inst_sel_renew                        solver
% 1.86/0.98  --inst_lit_activity_flag                true
% 1.86/0.98  --inst_restr_to_given                   false
% 1.86/0.98  --inst_activity_threshold               500
% 1.86/0.98  --inst_out_proof                        true
% 1.86/0.98  
% 1.86/0.98  ------ Resolution Options
% 1.86/0.98  
% 1.86/0.98  --resolution_flag                       true
% 1.86/0.98  --res_lit_sel                           adaptive
% 1.86/0.98  --res_lit_sel_side                      none
% 1.86/0.98  --res_ordering                          kbo
% 1.86/0.98  --res_to_prop_solver                    active
% 1.86/0.98  --res_prop_simpl_new                    false
% 1.86/0.98  --res_prop_simpl_given                  true
% 1.86/0.98  --res_passive_queue_type                priority_queues
% 1.86/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.86/0.98  --res_passive_queues_freq               [15;5]
% 1.86/0.98  --res_forward_subs                      full
% 1.86/0.98  --res_backward_subs                     full
% 1.86/0.98  --res_forward_subs_resolution           true
% 1.86/0.98  --res_backward_subs_resolution          true
% 1.86/0.98  --res_orphan_elimination                true
% 1.86/0.98  --res_time_limit                        2.
% 1.86/0.98  --res_out_proof                         true
% 1.86/0.98  
% 1.86/0.98  ------ Superposition Options
% 1.86/0.98  
% 1.86/0.98  --superposition_flag                    true
% 1.86/0.98  --sup_passive_queue_type                priority_queues
% 1.86/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.86/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.86/0.98  --demod_completeness_check              fast
% 1.86/0.98  --demod_use_ground                      true
% 1.86/0.98  --sup_to_prop_solver                    passive
% 1.86/0.98  --sup_prop_simpl_new                    true
% 1.86/0.98  --sup_prop_simpl_given                  true
% 1.86/0.98  --sup_fun_splitting                     false
% 1.86/0.98  --sup_smt_interval                      50000
% 1.86/0.98  
% 1.86/0.98  ------ Superposition Simplification Setup
% 1.86/0.98  
% 1.86/0.98  --sup_indices_passive                   []
% 1.86/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.86/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.98  --sup_full_bw                           [BwDemod]
% 1.86/0.98  --sup_immed_triv                        [TrivRules]
% 1.86/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.86/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.98  --sup_immed_bw_main                     []
% 1.86/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.86/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.98  
% 1.86/0.98  ------ Combination Options
% 1.86/0.98  
% 1.86/0.98  --comb_res_mult                         3
% 1.86/0.98  --comb_sup_mult                         2
% 1.86/0.98  --comb_inst_mult                        10
% 1.86/0.98  
% 1.86/0.98  ------ Debug Options
% 1.86/0.98  
% 1.86/0.98  --dbg_backtrace                         false
% 1.86/0.98  --dbg_dump_prop_clauses                 false
% 1.86/0.98  --dbg_dump_prop_clauses_file            -
% 1.86/0.98  --dbg_out_stat                          false
% 1.86/0.98  ------ Parsing...
% 1.86/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.86/0.98  ------ Proving...
% 1.86/0.98  ------ Problem Properties 
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  clauses                                 15
% 1.86/0.98  conjectures                             3
% 1.86/0.98  EPR                                     0
% 1.86/0.98  Horn                                    15
% 1.86/0.98  unary                                   2
% 1.86/0.98  binary                                  5
% 1.86/0.98  lits                                    38
% 1.86/0.98  lits eq                                 4
% 1.86/0.98  fd_pure                                 0
% 1.86/0.98  fd_pseudo                               0
% 1.86/0.98  fd_cond                                 0
% 1.86/0.98  fd_pseudo_cond                          1
% 1.86/0.98  AC symbols                              0
% 1.86/0.98  
% 1.86/0.98  ------ Schedule dynamic 5 is on 
% 1.86/0.98  
% 1.86/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  ------ 
% 1.86/0.98  Current options:
% 1.86/0.98  ------ 
% 1.86/0.98  
% 1.86/0.98  ------ Input Options
% 1.86/0.98  
% 1.86/0.98  --out_options                           all
% 1.86/0.98  --tptp_safe_out                         true
% 1.86/0.98  --problem_path                          ""
% 1.86/0.98  --include_path                          ""
% 1.86/0.98  --clausifier                            res/vclausify_rel
% 1.86/0.98  --clausifier_options                    --mode clausify
% 1.86/0.98  --stdin                                 false
% 1.86/0.98  --stats_out                             all
% 1.86/0.98  
% 1.86/0.98  ------ General Options
% 1.86/0.98  
% 1.86/0.98  --fof                                   false
% 1.86/0.98  --time_out_real                         305.
% 1.86/0.98  --time_out_virtual                      -1.
% 1.86/0.98  --symbol_type_check                     false
% 1.86/0.98  --clausify_out                          false
% 1.86/0.98  --sig_cnt_out                           false
% 1.86/0.98  --trig_cnt_out                          false
% 1.86/0.98  --trig_cnt_out_tolerance                1.
% 1.86/0.98  --trig_cnt_out_sk_spl                   false
% 1.86/0.98  --abstr_cl_out                          false
% 1.86/0.98  
% 1.86/0.98  ------ Global Options
% 1.86/0.98  
% 1.86/0.98  --schedule                              default
% 1.86/0.98  --add_important_lit                     false
% 1.86/0.98  --prop_solver_per_cl                    1000
% 1.86/0.98  --min_unsat_core                        false
% 1.86/0.98  --soft_assumptions                      false
% 1.86/0.98  --soft_lemma_size                       3
% 1.86/0.98  --prop_impl_unit_size                   0
% 1.86/0.98  --prop_impl_unit                        []
% 1.86/0.98  --share_sel_clauses                     true
% 1.86/0.98  --reset_solvers                         false
% 1.86/0.98  --bc_imp_inh                            [conj_cone]
% 1.86/0.98  --conj_cone_tolerance                   3.
% 1.86/0.98  --extra_neg_conj                        none
% 1.86/0.98  --large_theory_mode                     true
% 1.86/0.98  --prolific_symb_bound                   200
% 1.86/0.98  --lt_threshold                          2000
% 1.86/0.98  --clause_weak_htbl                      true
% 1.86/0.98  --gc_record_bc_elim                     false
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing Options
% 1.86/0.98  
% 1.86/0.98  --preprocessing_flag                    true
% 1.86/0.98  --time_out_prep_mult                    0.1
% 1.86/0.98  --splitting_mode                        input
% 1.86/0.98  --splitting_grd                         true
% 1.86/0.98  --splitting_cvd                         false
% 1.86/0.98  --splitting_cvd_svl                     false
% 1.86/0.98  --splitting_nvd                         32
% 1.86/0.98  --sub_typing                            true
% 1.86/0.98  --prep_gs_sim                           true
% 1.86/0.98  --prep_unflatten                        true
% 1.86/0.98  --prep_res_sim                          true
% 1.86/0.98  --prep_upred                            true
% 1.86/0.98  --prep_sem_filter                       exhaustive
% 1.86/0.98  --prep_sem_filter_out                   false
% 1.86/0.98  --pred_elim                             true
% 1.86/0.98  --res_sim_input                         true
% 1.86/0.98  --eq_ax_congr_red                       true
% 1.86/0.98  --pure_diseq_elim                       true
% 1.86/0.98  --brand_transform                       false
% 1.86/0.98  --non_eq_to_eq                          false
% 1.86/0.98  --prep_def_merge                        true
% 1.86/0.98  --prep_def_merge_prop_impl              false
% 1.86/0.98  --prep_def_merge_mbd                    true
% 1.86/0.98  --prep_def_merge_tr_red                 false
% 1.86/0.98  --prep_def_merge_tr_cl                  false
% 1.86/0.98  --smt_preprocessing                     true
% 1.86/0.98  --smt_ac_axioms                         fast
% 1.86/0.98  --preprocessed_out                      false
% 1.86/0.98  --preprocessed_stats                    false
% 1.86/0.98  
% 1.86/0.98  ------ Abstraction refinement Options
% 1.86/0.98  
% 1.86/0.98  --abstr_ref                             []
% 1.86/0.98  --abstr_ref_prep                        false
% 1.86/0.98  --abstr_ref_until_sat                   false
% 1.86/0.98  --abstr_ref_sig_restrict                funpre
% 1.86/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.86/0.98  --abstr_ref_under                       []
% 1.86/0.98  
% 1.86/0.98  ------ SAT Options
% 1.86/0.98  
% 1.86/0.98  --sat_mode                              false
% 1.86/0.98  --sat_fm_restart_options                ""
% 1.86/0.98  --sat_gr_def                            false
% 1.86/0.98  --sat_epr_types                         true
% 1.86/0.98  --sat_non_cyclic_types                  false
% 1.86/0.98  --sat_finite_models                     false
% 1.86/0.98  --sat_fm_lemmas                         false
% 1.86/0.98  --sat_fm_prep                           false
% 1.86/0.98  --sat_fm_uc_incr                        true
% 1.86/0.98  --sat_out_model                         small
% 1.86/0.98  --sat_out_clauses                       false
% 1.86/0.98  
% 1.86/0.98  ------ QBF Options
% 1.86/0.98  
% 1.86/0.98  --qbf_mode                              false
% 1.86/0.98  --qbf_elim_univ                         false
% 1.86/0.98  --qbf_dom_inst                          none
% 1.86/0.98  --qbf_dom_pre_inst                      false
% 1.86/0.98  --qbf_sk_in                             false
% 1.86/0.98  --qbf_pred_elim                         true
% 1.86/0.98  --qbf_split                             512
% 1.86/0.98  
% 1.86/0.98  ------ BMC1 Options
% 1.86/0.98  
% 1.86/0.98  --bmc1_incremental                      false
% 1.86/0.98  --bmc1_axioms                           reachable_all
% 1.86/0.98  --bmc1_min_bound                        0
% 1.86/0.98  --bmc1_max_bound                        -1
% 1.86/0.98  --bmc1_max_bound_default                -1
% 1.86/0.98  --bmc1_symbol_reachability              true
% 1.86/0.98  --bmc1_property_lemmas                  false
% 1.86/0.98  --bmc1_k_induction                      false
% 1.86/0.98  --bmc1_non_equiv_states                 false
% 1.86/0.98  --bmc1_deadlock                         false
% 1.86/0.98  --bmc1_ucm                              false
% 1.86/0.98  --bmc1_add_unsat_core                   none
% 1.86/0.98  --bmc1_unsat_core_children              false
% 1.86/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.86/0.98  --bmc1_out_stat                         full
% 1.86/0.98  --bmc1_ground_init                      false
% 1.86/0.98  --bmc1_pre_inst_next_state              false
% 1.86/0.98  --bmc1_pre_inst_state                   false
% 1.86/0.98  --bmc1_pre_inst_reach_state             false
% 1.86/0.98  --bmc1_out_unsat_core                   false
% 1.86/0.98  --bmc1_aig_witness_out                  false
% 1.86/0.98  --bmc1_verbose                          false
% 1.86/0.98  --bmc1_dump_clauses_tptp                false
% 1.86/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.86/0.98  --bmc1_dump_file                        -
% 1.86/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.86/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.86/0.98  --bmc1_ucm_extend_mode                  1
% 1.86/0.98  --bmc1_ucm_init_mode                    2
% 1.86/0.98  --bmc1_ucm_cone_mode                    none
% 1.86/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.86/0.98  --bmc1_ucm_relax_model                  4
% 1.86/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.86/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.86/0.98  --bmc1_ucm_layered_model                none
% 1.86/0.98  --bmc1_ucm_max_lemma_size               10
% 1.86/0.98  
% 1.86/0.98  ------ AIG Options
% 1.86/0.98  
% 1.86/0.98  --aig_mode                              false
% 1.86/0.98  
% 1.86/0.98  ------ Instantiation Options
% 1.86/0.98  
% 1.86/0.98  --instantiation_flag                    true
% 1.86/0.98  --inst_sos_flag                         false
% 1.86/0.98  --inst_sos_phase                        true
% 1.86/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.86/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.86/0.98  --inst_lit_sel_side                     none
% 1.86/0.98  --inst_solver_per_active                1400
% 1.86/0.98  --inst_solver_calls_frac                1.
% 1.86/0.98  --inst_passive_queue_type               priority_queues
% 1.86/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.86/0.98  --inst_passive_queues_freq              [25;2]
% 1.86/0.98  --inst_dismatching                      true
% 1.86/0.98  --inst_eager_unprocessed_to_passive     true
% 1.86/0.98  --inst_prop_sim_given                   true
% 1.86/0.98  --inst_prop_sim_new                     false
% 1.86/0.98  --inst_subs_new                         false
% 1.86/0.98  --inst_eq_res_simp                      false
% 1.86/0.98  --inst_subs_given                       false
% 1.86/0.98  --inst_orphan_elimination               true
% 1.86/0.98  --inst_learning_loop_flag               true
% 1.86/0.98  --inst_learning_start                   3000
% 1.86/0.98  --inst_learning_factor                  2
% 1.86/0.98  --inst_start_prop_sim_after_learn       3
% 1.86/0.98  --inst_sel_renew                        solver
% 1.86/0.98  --inst_lit_activity_flag                true
% 1.86/0.98  --inst_restr_to_given                   false
% 1.86/0.98  --inst_activity_threshold               500
% 1.86/0.98  --inst_out_proof                        true
% 1.86/0.98  
% 1.86/0.98  ------ Resolution Options
% 1.86/0.98  
% 1.86/0.98  --resolution_flag                       false
% 1.86/0.98  --res_lit_sel                           adaptive
% 1.86/0.98  --res_lit_sel_side                      none
% 1.86/0.98  --res_ordering                          kbo
% 1.86/0.98  --res_to_prop_solver                    active
% 1.86/0.98  --res_prop_simpl_new                    false
% 1.86/0.98  --res_prop_simpl_given                  true
% 1.86/0.98  --res_passive_queue_type                priority_queues
% 1.86/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.86/0.98  --res_passive_queues_freq               [15;5]
% 1.86/0.98  --res_forward_subs                      full
% 1.86/0.98  --res_backward_subs                     full
% 1.86/0.98  --res_forward_subs_resolution           true
% 1.86/0.98  --res_backward_subs_resolution          true
% 1.86/0.98  --res_orphan_elimination                true
% 1.86/0.98  --res_time_limit                        2.
% 1.86/0.98  --res_out_proof                         true
% 1.86/0.98  
% 1.86/0.98  ------ Superposition Options
% 1.86/0.98  
% 1.86/0.98  --superposition_flag                    true
% 1.86/0.98  --sup_passive_queue_type                priority_queues
% 1.86/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.86/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.86/0.98  --demod_completeness_check              fast
% 1.86/0.98  --demod_use_ground                      true
% 1.86/0.98  --sup_to_prop_solver                    passive
% 1.86/0.98  --sup_prop_simpl_new                    true
% 1.86/0.98  --sup_prop_simpl_given                  true
% 1.86/0.98  --sup_fun_splitting                     false
% 1.86/0.98  --sup_smt_interval                      50000
% 1.86/0.98  
% 1.86/0.98  ------ Superposition Simplification Setup
% 1.86/0.98  
% 1.86/0.98  --sup_indices_passive                   []
% 1.86/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.86/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.98  --sup_full_bw                           [BwDemod]
% 1.86/0.98  --sup_immed_triv                        [TrivRules]
% 1.86/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.86/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.98  --sup_immed_bw_main                     []
% 1.86/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.86/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.98  
% 1.86/0.98  ------ Combination Options
% 1.86/0.98  
% 1.86/0.98  --comb_res_mult                         3
% 1.86/0.98  --comb_sup_mult                         2
% 1.86/0.98  --comb_inst_mult                        10
% 1.86/0.98  
% 1.86/0.98  ------ Debug Options
% 1.86/0.98  
% 1.86/0.98  --dbg_backtrace                         false
% 1.86/0.98  --dbg_dump_prop_clauses                 false
% 1.86/0.98  --dbg_dump_prop_clauses_file            -
% 1.86/0.98  --dbg_out_stat                          false
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  ------ Proving...
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  % SZS status Theorem for theBenchmark.p
% 1.86/0.98  
% 1.86/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.86/0.98  
% 1.86/0.98  fof(f4,axiom,(
% 1.86/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f17,plain,(
% 1.86/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.86/0.98    inference(ennf_transformation,[],[f4])).
% 1.86/0.98  
% 1.86/0.98  fof(f28,plain,(
% 1.86/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.86/0.98    inference(nnf_transformation,[],[f17])).
% 1.86/0.98  
% 1.86/0.98  fof(f29,plain,(
% 1.86/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.86/0.98    inference(rectify,[],[f28])).
% 1.86/0.98  
% 1.86/0.98  fof(f30,plain,(
% 1.86/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 1.86/0.98    introduced(choice_axiom,[])).
% 1.86/0.98  
% 1.86/0.98  fof(f31,plain,(
% 1.86/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.86/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 1.86/0.98  
% 1.86/0.98  fof(f41,plain,(
% 1.86/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.86/0.98    inference(cnf_transformation,[],[f31])).
% 1.86/0.98  
% 1.86/0.98  fof(f10,conjecture,(
% 1.86/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f11,negated_conjecture,(
% 1.86/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.86/0.98    inference(negated_conjecture,[],[f10])).
% 1.86/0.98  
% 1.86/0.98  fof(f12,plain,(
% 1.86/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.86/0.98    inference(pure_predicate_removal,[],[f11])).
% 1.86/0.98  
% 1.86/0.98  fof(f24,plain,(
% 1.86/0.98    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)))),
% 1.86/0.98    inference(ennf_transformation,[],[f12])).
% 1.86/0.98  
% 1.86/0.98  fof(f25,plain,(
% 1.86/0.98    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3))),
% 1.86/0.98    inference(flattening,[],[f24])).
% 1.86/0.98  
% 1.86/0.98  fof(f34,plain,(
% 1.86/0.98    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK4,X4) != sK1 | ~m1_subset_1(X4,sK2)) & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4))),
% 1.86/0.98    introduced(choice_axiom,[])).
% 1.86/0.98  
% 1.86/0.98  fof(f35,plain,(
% 1.86/0.98    ! [X4] : (k1_funct_1(sK4,X4) != sK1 | ~m1_subset_1(X4,sK2)) & r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_1(sK4)),
% 1.86/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f34])).
% 1.86/0.98  
% 1.86/0.98  fof(f53,plain,(
% 1.86/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 1.86/0.98    inference(cnf_transformation,[],[f35])).
% 1.86/0.98  
% 1.86/0.98  fof(f1,axiom,(
% 1.86/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f26,plain,(
% 1.86/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.86/0.98    inference(nnf_transformation,[],[f1])).
% 1.86/0.98  
% 1.86/0.98  fof(f37,plain,(
% 1.86/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.86/0.98    inference(cnf_transformation,[],[f26])).
% 1.86/0.98  
% 1.86/0.98  fof(f8,axiom,(
% 1.86/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f13,plain,(
% 1.86/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.86/0.98    inference(pure_predicate_removal,[],[f8])).
% 1.86/0.98  
% 1.86/0.98  fof(f22,plain,(
% 1.86/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.98    inference(ennf_transformation,[],[f13])).
% 1.86/0.98  
% 1.86/0.98  fof(f50,plain,(
% 1.86/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.86/0.98    inference(cnf_transformation,[],[f22])).
% 1.86/0.98  
% 1.86/0.98  fof(f3,axiom,(
% 1.86/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f16,plain,(
% 1.86/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.86/0.98    inference(ennf_transformation,[],[f3])).
% 1.86/0.98  
% 1.86/0.98  fof(f27,plain,(
% 1.86/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.86/0.98    inference(nnf_transformation,[],[f16])).
% 1.86/0.98  
% 1.86/0.98  fof(f39,plain,(
% 1.86/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.86/0.98    inference(cnf_transformation,[],[f27])).
% 1.86/0.98  
% 1.86/0.98  fof(f7,axiom,(
% 1.86/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f21,plain,(
% 1.86/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.98    inference(ennf_transformation,[],[f7])).
% 1.86/0.98  
% 1.86/0.98  fof(f49,plain,(
% 1.86/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.86/0.98    inference(cnf_transformation,[],[f21])).
% 1.86/0.98  
% 1.86/0.98  fof(f2,axiom,(
% 1.86/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f14,plain,(
% 1.86/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.86/0.98    inference(ennf_transformation,[],[f2])).
% 1.86/0.98  
% 1.86/0.98  fof(f15,plain,(
% 1.86/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.86/0.98    inference(flattening,[],[f14])).
% 1.86/0.98  
% 1.86/0.98  fof(f38,plain,(
% 1.86/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.86/0.98    inference(cnf_transformation,[],[f15])).
% 1.86/0.98  
% 1.86/0.98  fof(f9,axiom,(
% 1.86/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f23,plain,(
% 1.86/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.98    inference(ennf_transformation,[],[f9])).
% 1.86/0.98  
% 1.86/0.98  fof(f51,plain,(
% 1.86/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.86/0.98    inference(cnf_transformation,[],[f23])).
% 1.86/0.98  
% 1.86/0.98  fof(f54,plain,(
% 1.86/0.98    r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4))),
% 1.86/0.98    inference(cnf_transformation,[],[f35])).
% 1.86/0.98  
% 1.86/0.98  fof(f5,axiom,(
% 1.86/0.98    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f18,plain,(
% 1.86/0.98    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.86/0.98    inference(ennf_transformation,[],[f5])).
% 1.86/0.98  
% 1.86/0.98  fof(f45,plain,(
% 1.86/0.98    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.86/0.98    inference(cnf_transformation,[],[f18])).
% 1.86/0.98  
% 1.86/0.98  fof(f42,plain,(
% 1.86/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.86/0.98    inference(cnf_transformation,[],[f31])).
% 1.86/0.98  
% 1.86/0.98  fof(f6,axiom,(
% 1.86/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.98  
% 1.86/0.98  fof(f19,plain,(
% 1.86/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.86/0.98    inference(ennf_transformation,[],[f6])).
% 1.86/0.98  
% 1.86/0.98  fof(f20,plain,(
% 1.86/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.86/0.98    inference(flattening,[],[f19])).
% 1.86/0.98  
% 1.86/0.98  fof(f32,plain,(
% 1.86/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.86/0.98    inference(nnf_transformation,[],[f20])).
% 1.86/0.98  
% 1.86/0.98  fof(f33,plain,(
% 1.86/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.86/0.98    inference(flattening,[],[f32])).
% 1.86/0.98  
% 1.86/0.98  fof(f47,plain,(
% 1.86/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.86/0.98    inference(cnf_transformation,[],[f33])).
% 1.86/0.98  
% 1.86/0.98  fof(f52,plain,(
% 1.86/0.98    v1_funct_1(sK4)),
% 1.86/0.98    inference(cnf_transformation,[],[f35])).
% 1.86/0.98  
% 1.86/0.98  fof(f55,plain,(
% 1.86/0.98    ( ! [X4] : (k1_funct_1(sK4,X4) != sK1 | ~m1_subset_1(X4,sK2)) )),
% 1.86/0.98    inference(cnf_transformation,[],[f35])).
% 1.86/0.98  
% 1.86/0.98  cnf(c_8,plain,
% 1.86/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.86/0.98      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 1.86/0.98      | ~ v1_relat_1(X1) ),
% 1.86/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1053,plain,
% 1.86/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 1.86/0.98      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 1.86/0.98      | v1_relat_1(X1) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_18,negated_conjecture,
% 1.86/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 1.86/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1047,plain,
% 1.86/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_0,plain,
% 1.86/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.86/0.98      inference(cnf_transformation,[],[f37]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_163,plain,
% 1.86/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.86/0.98      inference(prop_impl,[status(thm)],[c_0]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_14,plain,
% 1.86/0.98      ( v4_relat_1(X0,X1)
% 1.86/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.86/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_4,plain,
% 1.86/0.98      ( ~ v4_relat_1(X0,X1)
% 1.86/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 1.86/0.98      | ~ v1_relat_1(X0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_279,plain,
% 1.86/0.98      ( r1_tarski(k1_relat_1(X0),X1)
% 1.86/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.98      | ~ v1_relat_1(X0) ),
% 1.86/0.98      inference(resolution,[status(thm)],[c_14,c_4]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_13,plain,
% 1.86/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.98      | v1_relat_1(X0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_283,plain,
% 1.86/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 1.86/0.98      inference(global_propositional_subsumption,
% 1.86/0.98                [status(thm)],
% 1.86/0.98                [c_279,c_14,c_13,c_4]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_284,plain,
% 1.86/0.98      ( r1_tarski(k1_relat_1(X0),X1)
% 1.86/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.86/0.98      inference(renaming,[status(thm)],[c_283]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_301,plain,
% 1.86/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.86/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 1.86/0.98      | X3 != X1
% 1.86/0.98      | k1_relat_1(X2) != X0 ),
% 1.86/0.98      inference(resolution_lifted,[status(thm)],[c_163,c_284]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_302,plain,
% 1.86/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.98      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) ),
% 1.86/0.98      inference(unflattening,[status(thm)],[c_301]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1046,plain,
% 1.86/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.86/0.98      | m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1)) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_302]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1361,plain,
% 1.86/0.98      ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_1047,c_1046]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2,plain,
% 1.86/0.98      ( ~ r2_hidden(X0,X1)
% 1.86/0.98      | m1_subset_1(X0,X2)
% 1.86/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 1.86/0.98      inference(cnf_transformation,[],[f38]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1057,plain,
% 1.86/0.98      ( r2_hidden(X0,X1) != iProver_top
% 1.86/0.98      | m1_subset_1(X0,X2) = iProver_top
% 1.86/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1472,plain,
% 1.86/0.98      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 1.86/0.98      | m1_subset_1(X0,sK2) = iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_1361,c_1057]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1621,plain,
% 1.86/0.98      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.86/0.98      | m1_subset_1(sK0(X0,X1,sK4),sK2) = iProver_top
% 1.86/0.98      | v1_relat_1(sK4) != iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_1053,c_1472]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_21,plain,
% 1.86/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1167,plain,
% 1.86/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 1.86/0.98      | v1_relat_1(sK4) ),
% 1.86/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1168,plain,
% 1.86/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 1.86/0.98      | v1_relat_1(sK4) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_1167]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1675,plain,
% 1.86/0.98      ( m1_subset_1(sK0(X0,X1,sK4),sK2) = iProver_top
% 1.86/0.98      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 1.86/0.98      inference(global_propositional_subsumption,
% 1.86/0.98                [status(thm)],
% 1.86/0.98                [c_1621,c_21,c_1168]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1676,plain,
% 1.86/0.98      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.86/0.98      | m1_subset_1(sK0(X0,X1,sK4),sK2) = iProver_top ),
% 1.86/0.98      inference(renaming,[status(thm)],[c_1675]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_15,plain,
% 1.86/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1050,plain,
% 1.86/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.86/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1366,plain,
% 1.86/0.98      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_1047,c_1050]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_17,negated_conjecture,
% 1.86/0.98      ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) ),
% 1.86/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1048,plain,
% 1.86/0.98      ( r2_hidden(sK1,k2_relset_1(sK2,sK3,sK4)) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1477,plain,
% 1.86/0.98      ( r2_hidden(sK1,k2_relat_1(sK4)) = iProver_top ),
% 1.86/0.98      inference(demodulation,[status(thm)],[c_1366,c_1048]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1051,plain,
% 1.86/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.86/0.98      | v1_relat_1(X0) = iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1259,plain,
% 1.86/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_1047,c_1051]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_9,plain,
% 1.86/0.98      ( ~ v1_relat_1(X0)
% 1.86/0.98      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 1.86/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1052,plain,
% 1.86/0.98      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 1.86/0.98      | v1_relat_1(X0) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1456,plain,
% 1.86/0.98      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_1259,c_1052]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_7,plain,
% 1.86/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.86/0.98      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 1.86/0.98      | ~ v1_relat_1(X1) ),
% 1.86/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1054,plain,
% 1.86/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 1.86/0.98      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 1.86/0.98      | v1_relat_1(X1) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_11,plain,
% 1.86/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 1.86/0.98      | ~ v1_funct_1(X2)
% 1.86/0.98      | ~ v1_relat_1(X2)
% 1.86/0.98      | k1_funct_1(X2,X0) = X1 ),
% 1.86/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_19,negated_conjecture,
% 1.86/0.98      ( v1_funct_1(sK4) ),
% 1.86/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_316,plain,
% 1.86/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 1.86/0.98      | ~ v1_relat_1(X2)
% 1.86/0.98      | k1_funct_1(X2,X0) = X1
% 1.86/0.98      | sK4 != X2 ),
% 1.86/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_317,plain,
% 1.86/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 1.86/0.98      | ~ v1_relat_1(sK4)
% 1.86/0.98      | k1_funct_1(sK4,X0) = X1 ),
% 1.86/0.98      inference(unflattening,[status(thm)],[c_316]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1045,plain,
% 1.86/0.98      ( k1_funct_1(sK4,X0) = X1
% 1.86/0.98      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 1.86/0.98      | v1_relat_1(sK4) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_318,plain,
% 1.86/0.98      ( k1_funct_1(sK4,X0) = X1
% 1.86/0.98      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 1.86/0.98      | v1_relat_1(sK4) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1189,plain,
% 1.86/0.98      ( r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 1.86/0.98      | k1_funct_1(sK4,X0) = X1 ),
% 1.86/0.98      inference(global_propositional_subsumption,
% 1.86/0.98                [status(thm)],
% 1.86/0.98                [c_1045,c_21,c_318,c_1168]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1190,plain,
% 1.86/0.98      ( k1_funct_1(sK4,X0) = X1
% 1.86/0.98      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
% 1.86/0.98      inference(renaming,[status(thm)],[c_1189]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1688,plain,
% 1.86/0.98      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 1.86/0.98      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.86/0.98      | v1_relat_1(sK4) != iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_1054,c_1190]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1806,plain,
% 1.86/0.98      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.86/0.98      | k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0 ),
% 1.86/0.98      inference(global_propositional_subsumption,
% 1.86/0.98                [status(thm)],
% 1.86/0.98                [c_1688,c_21,c_1168]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1807,plain,
% 1.86/0.98      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 1.86/0.98      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 1.86/0.98      inference(renaming,[status(thm)],[c_1806]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1816,plain,
% 1.86/0.98      ( k1_funct_1(sK4,sK0(X0,k1_relat_1(sK4),sK4)) = X0
% 1.86/0.98      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_1456,c_1807]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2003,plain,
% 1.86/0.98      ( k1_funct_1(sK4,sK0(sK1,k1_relat_1(sK4),sK4)) = sK1 ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_1477,c_1816]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_16,negated_conjecture,
% 1.86/0.98      ( ~ m1_subset_1(X0,sK2) | k1_funct_1(sK4,X0) != sK1 ),
% 1.86/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_1049,plain,
% 1.86/0.98      ( k1_funct_1(sK4,X0) != sK1 | m1_subset_1(X0,sK2) != iProver_top ),
% 1.86/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2036,plain,
% 1.86/0.98      ( m1_subset_1(sK0(sK1,k1_relat_1(sK4),sK4),sK2) != iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_2003,c_1049]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2136,plain,
% 1.86/0.98      ( r2_hidden(sK1,k9_relat_1(sK4,k1_relat_1(sK4))) != iProver_top ),
% 1.86/0.98      inference(superposition,[status(thm)],[c_1676,c_2036]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(c_2138,plain,
% 1.86/0.98      ( r2_hidden(sK1,k2_relat_1(sK4)) != iProver_top ),
% 1.86/0.98      inference(light_normalisation,[status(thm)],[c_2136,c_1456]) ).
% 1.86/0.98  
% 1.86/0.98  cnf(contradiction,plain,
% 1.86/0.98      ( $false ),
% 1.86/0.98      inference(minisat,[status(thm)],[c_2138,c_1477]) ).
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.86/0.98  
% 1.86/0.98  ------                               Statistics
% 1.86/0.98  
% 1.86/0.98  ------ General
% 1.86/0.98  
% 1.86/0.98  abstr_ref_over_cycles:                  0
% 1.86/0.98  abstr_ref_under_cycles:                 0
% 1.86/0.98  gc_basic_clause_elim:                   0
% 1.86/0.98  forced_gc_time:                         0
% 1.86/0.98  parsing_time:                           0.008
% 1.86/0.98  unif_index_cands_time:                  0.
% 1.86/0.98  unif_index_add_time:                    0.
% 1.86/0.98  orderings_time:                         0.
% 1.86/0.98  out_proof_time:                         0.01
% 1.86/0.98  total_time:                             0.094
% 1.86/0.98  num_of_symbols:                         50
% 1.86/0.98  num_of_terms:                           1532
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing
% 1.86/0.98  
% 1.86/0.98  num_of_splits:                          0
% 1.86/0.98  num_of_split_atoms:                     0
% 1.86/0.98  num_of_reused_defs:                     0
% 1.86/0.98  num_eq_ax_congr_red:                    23
% 1.86/0.98  num_of_sem_filtered_clauses:            1
% 1.86/0.98  num_of_subtypes:                        0
% 1.86/0.98  monotx_restored_types:                  0
% 1.86/0.98  sat_num_of_epr_types:                   0
% 1.86/0.98  sat_num_of_non_cyclic_types:            0
% 1.86/0.98  sat_guarded_non_collapsed_types:        0
% 1.86/0.98  num_pure_diseq_elim:                    0
% 1.86/0.98  simp_replaced_by:                       0
% 1.86/0.98  res_preprocessed:                       90
% 1.86/0.98  prep_upred:                             0
% 1.86/0.98  prep_unflattend:                        19
% 1.86/0.98  smt_new_axioms:                         0
% 1.86/0.98  pred_elim_cands:                        3
% 1.86/0.98  pred_elim:                              3
% 1.86/0.98  pred_elim_cl:                           5
% 1.86/0.98  pred_elim_cycles:                       5
% 1.86/0.98  merged_defs:                            2
% 1.86/0.98  merged_defs_ncl:                        0
% 1.86/0.98  bin_hyper_res:                          2
% 1.86/0.98  prep_cycles:                            4
% 1.86/0.98  pred_elim_time:                         0.006
% 1.86/0.98  splitting_time:                         0.
% 1.86/0.98  sem_filter_time:                        0.
% 1.86/0.98  monotx_time:                            0.001
% 1.86/0.98  subtype_inf_time:                       0.
% 1.86/0.98  
% 1.86/0.98  ------ Problem properties
% 1.86/0.98  
% 1.86/0.98  clauses:                                15
% 1.86/0.98  conjectures:                            3
% 1.86/0.98  epr:                                    0
% 1.86/0.98  horn:                                   15
% 1.86/0.98  ground:                                 2
% 1.86/0.98  unary:                                  2
% 1.86/0.98  binary:                                 5
% 1.86/0.98  lits:                                   38
% 1.86/0.98  lits_eq:                                4
% 1.86/0.98  fd_pure:                                0
% 1.86/0.98  fd_pseudo:                              0
% 1.86/0.98  fd_cond:                                0
% 1.86/0.98  fd_pseudo_cond:                         1
% 1.86/0.98  ac_symbols:                             0
% 1.86/0.98  
% 1.86/0.98  ------ Propositional Solver
% 1.86/0.98  
% 1.86/0.98  prop_solver_calls:                      26
% 1.86/0.98  prop_fast_solver_calls:                 614
% 1.86/0.98  smt_solver_calls:                       0
% 1.86/0.98  smt_fast_solver_calls:                  0
% 1.86/0.98  prop_num_of_clauses:                    577
% 1.86/0.98  prop_preprocess_simplified:             3097
% 1.86/0.99  prop_fo_subsumed:                       7
% 1.86/0.99  prop_solver_time:                       0.
% 1.86/0.99  smt_solver_time:                        0.
% 1.86/0.99  smt_fast_solver_time:                   0.
% 1.86/0.99  prop_fast_solver_time:                  0.
% 1.86/0.99  prop_unsat_core_time:                   0.
% 1.86/0.99  
% 1.86/0.99  ------ QBF
% 1.86/0.99  
% 1.86/0.99  qbf_q_res:                              0
% 1.86/0.99  qbf_num_tautologies:                    0
% 1.86/0.99  qbf_prep_cycles:                        0
% 1.86/0.99  
% 1.86/0.99  ------ BMC1
% 1.86/0.99  
% 1.86/0.99  bmc1_current_bound:                     -1
% 1.86/0.99  bmc1_last_solved_bound:                 -1
% 1.86/0.99  bmc1_unsat_core_size:                   -1
% 1.86/0.99  bmc1_unsat_core_parents_size:           -1
% 1.86/0.99  bmc1_merge_next_fun:                    0
% 1.86/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.86/0.99  
% 1.86/0.99  ------ Instantiation
% 1.86/0.99  
% 1.86/0.99  inst_num_of_clauses:                    171
% 1.86/0.99  inst_num_in_passive:                    23
% 1.86/0.99  inst_num_in_active:                     139
% 1.86/0.99  inst_num_in_unprocessed:                10
% 1.86/0.99  inst_num_of_loops:                      160
% 1.86/0.99  inst_num_of_learning_restarts:          0
% 1.86/0.99  inst_num_moves_active_passive:          16
% 1.86/0.99  inst_lit_activity:                      0
% 1.86/0.99  inst_lit_activity_moves:                0
% 1.86/0.99  inst_num_tautologies:                   0
% 1.86/0.99  inst_num_prop_implied:                  0
% 1.86/0.99  inst_num_existing_simplified:           0
% 1.86/0.99  inst_num_eq_res_simplified:             0
% 1.86/0.99  inst_num_child_elim:                    0
% 1.86/0.99  inst_num_of_dismatching_blockings:      35
% 1.86/0.99  inst_num_of_non_proper_insts:           154
% 1.86/0.99  inst_num_of_duplicates:                 0
% 1.86/0.99  inst_inst_num_from_inst_to_res:         0
% 1.86/0.99  inst_dismatching_checking_time:         0.
% 1.86/0.99  
% 1.86/0.99  ------ Resolution
% 1.86/0.99  
% 1.86/0.99  res_num_of_clauses:                     0
% 1.86/0.99  res_num_in_passive:                     0
% 1.86/0.99  res_num_in_active:                      0
% 1.86/0.99  res_num_of_loops:                       94
% 1.86/0.99  res_forward_subset_subsumed:            24
% 1.86/0.99  res_backward_subset_subsumed:           2
% 1.86/0.99  res_forward_subsumed:                   0
% 1.86/0.99  res_backward_subsumed:                  0
% 1.86/0.99  res_forward_subsumption_resolution:     0
% 1.86/0.99  res_backward_subsumption_resolution:    0
% 1.86/0.99  res_clause_to_clause_subsumption:       51
% 1.86/0.99  res_orphan_elimination:                 0
% 1.86/0.99  res_tautology_del:                      42
% 1.86/0.99  res_num_eq_res_simplified:              0
% 1.86/0.99  res_num_sel_changes:                    0
% 1.86/0.99  res_moves_from_active_to_pass:          0
% 1.86/0.99  
% 1.86/0.99  ------ Superposition
% 1.86/0.99  
% 1.86/0.99  sup_time_total:                         0.
% 1.86/0.99  sup_time_generating:                    0.
% 1.86/0.99  sup_time_sim_full:                      0.
% 1.86/0.99  sup_time_sim_immed:                     0.
% 1.86/0.99  
% 1.86/0.99  sup_num_of_clauses:                     40
% 1.86/0.99  sup_num_in_active:                      30
% 1.86/0.99  sup_num_in_passive:                     10
% 1.86/0.99  sup_num_of_loops:                       30
% 1.86/0.99  sup_fw_superposition:                   18
% 1.86/0.99  sup_bw_superposition:                   12
% 1.86/0.99  sup_immediate_simplified:               4
% 1.86/0.99  sup_given_eliminated:                   0
% 1.86/0.99  comparisons_done:                       0
% 1.86/0.99  comparisons_avoided:                    0
% 1.86/0.99  
% 1.86/0.99  ------ Simplifications
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  sim_fw_subset_subsumed:                 2
% 1.86/0.99  sim_bw_subset_subsumed:                 0
% 1.86/0.99  sim_fw_subsumed:                        1
% 1.86/0.99  sim_bw_subsumed:                        0
% 1.86/0.99  sim_fw_subsumption_res:                 0
% 1.86/0.99  sim_bw_subsumption_res:                 0
% 1.86/0.99  sim_tautology_del:                      1
% 1.86/0.99  sim_eq_tautology_del:                   1
% 1.86/0.99  sim_eq_res_simp:                        0
% 1.86/0.99  sim_fw_demodulated:                     0
% 1.86/0.99  sim_bw_demodulated:                     1
% 1.86/0.99  sim_light_normalised:                   2
% 1.86/0.99  sim_joinable_taut:                      0
% 1.86/0.99  sim_joinable_simp:                      0
% 1.86/0.99  sim_ac_normalised:                      0
% 1.86/0.99  sim_smt_subsumption:                    0
% 1.86/0.99  
%------------------------------------------------------------------------------
