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
% DateTime   : Thu Dec  3 12:01:01 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 689 expanded)
%              Number of clauses        :   72 ( 252 expanded)
%              Number of leaves         :   11 ( 123 expanded)
%              Depth                    :   23
%              Number of atoms          :  327 (2509 expanded)
%              Number of equality atoms :  125 ( 607 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK4,X4) != sK3
          | ~ r2_hidden(X4,sK1) )
      & r2_hidden(sK3,k2_relset_1(sK1,sK2,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ! [X4] :
        ( k1_funct_1(sK4,X4) != sK3
        | ~ r2_hidden(X4,sK1) )
    & r2_hidden(sK3,k2_relset_1(sK1,sK2,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f29])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,(
    r2_hidden(sK3,k2_relset_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X4] :
      ( k1_funct_1(sK4,X4) != sK3
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_225,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_226,plain,
    ( v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_373,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),X2)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_226])).

cnf(c_374,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(sK0(X0,X1,sK4),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_524,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(sK0(X0,X1,sK4),X1)
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_374])).

cnf(c_910,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),X1) = iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_525,plain,
    ( sP3_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_374])).

cnf(c_575,plain,
    ( sP3_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_576,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),X1) = iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_537,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1077,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_537])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_410,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k2_relat_1(k7_relat_1(X2,X3)) = k9_relat_1(X2,X3)
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_226])).

cnf(c_411,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k2_relat_1(k7_relat_1(sK4,X2)) = k9_relat_1(sK4,X2) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_520,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_411])).

cnf(c_1078,plain,
    ( ~ sP1_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_1081,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1078])).

cnf(c_1287,plain,
    ( r2_hidden(sK0(X0,X1,sK4),X1) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_910,c_575,c_576,c_1077,c_1081])).

cnf(c_1288,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(sK0(X0,X1,sK4),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1287])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_216,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_217,plain,
    ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_1076,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_217])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_927,plain,
    ( r2_hidden(sK3,k2_relset_1(sK1,sK2,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1094,plain,
    ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1076,c_927])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_187,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_10,c_5])).

cnf(c_191,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_187,c_10,c_9,c_5])).

cnf(c_207,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_191,c_14])).

cnf(c_208,plain,
    ( k7_relat_1(sK4,X0) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_207])).

cnf(c_1073,plain,
    ( k7_relat_1(sK4,sK1) = sK4 ),
    inference(equality_resolution,[status(thm)],[c_208])).

cnf(c_519,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_411])).

cnf(c_905,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0)
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_521,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_411])).

cnf(c_1115,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_521,c_519,c_1077,c_1078])).

cnf(c_1119,plain,
    ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1073,c_1115])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_358,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_226])).

cnf(c_359,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(sK0(X0,X1,sK4),X0),sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_526,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
    | r2_hidden(k4_tarski(sK0(X0,X1,sK4),X0),sK4)
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_359])).

cnf(c_913,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,sK4),X0),sK4) = iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_527,plain,
    ( sP4_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_359])).

cnf(c_580,plain,
    ( sP4_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_581,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,sK4),X0),sK4) = iProver_top
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_1392,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1,sK4),X0),sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_913,c_580,c_581,c_1077,c_1081])).

cnf(c_1393,plain,
    ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X1,sK4),X0),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_1392])).

cnf(c_7,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_274,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_275,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | ~ v1_relat_1(sK4)
    | k1_funct_1(sK4,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_301,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | k1_funct_1(sK4,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[status(thm)],[c_226,c_275])).

cnf(c_534,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
    | k1_funct_1(sK4,X0) = X1
    | ~ sP8_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP8_iProver_split])],[c_301])).

cnf(c_925,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | sP8_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_535,plain,
    ( sP8_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_301])).

cnf(c_600,plain,
    ( sP8_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_601,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | sP8_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_1267,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
    | k1_funct_1(sK4,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_925,c_600,c_601,c_1077,c_1081])).

cnf(c_1268,plain,
    ( k1_funct_1(sK4,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_1267])).

cnf(c_1401,plain,
    ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
    | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_1268])).

cnf(c_1597,plain,
    ( k1_funct_1(sK4,sK0(X0,sK1,sK4)) = X0
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1119,c_1401])).

cnf(c_1682,plain,
    ( k1_funct_1(sK4,sK0(sK3,sK1,sK4)) = sK3 ),
    inference(superposition,[status(thm)],[c_1094,c_1597])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | k1_funct_1(sK4,X0) != sK3 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_928,plain,
    ( k1_funct_1(sK4,X0) != sK3
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1694,plain,
    ( r2_hidden(sK0(sK3,sK1,sK4),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1682,c_928])).

cnf(c_1761,plain,
    ( r2_hidden(sK3,k9_relat_1(sK4,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_1694])).

cnf(c_1762,plain,
    ( r2_hidden(sK3,k2_relat_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1761,c_1119])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1762,c_1094])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:05:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
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
% 1.86/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing... gs_s  sp: 16 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.86/0.98  
% 1.86/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.86/0.98  ------ Proving...
% 1.86/0.98  ------ Problem Properties 
% 1.86/0.98  
% 1.86/0.98  
% 1.86/0.98  clauses                                 28
% 1.86/0.98  conjectures                             2
% 1.86/0.98  EPR                                     8
% 1.86/0.98  Horn                                    20
% 1.86/0.98  unary                                   1
% 1.86/0.98  binary                                  20
% 1.86/0.98  lits                                    63
% 1.86/0.98  lits eq                                 15
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
% 1.86/0.99  --inst_passive_queues_freq              [25;2]
% 1.86/0.99  --inst_dismatching                      true
% 1.86/0.99  --inst_eager_unprocessed_to_passive     true
% 1.86/0.99  --inst_prop_sim_given                   true
% 1.86/0.99  --inst_prop_sim_new                     false
% 1.86/0.99  --inst_subs_new                         false
% 1.86/0.99  --inst_eq_res_simp                      false
% 1.86/0.99  --inst_subs_given                       false
% 1.86/0.99  --inst_orphan_elimination               true
% 1.86/0.99  --inst_learning_loop_flag               true
% 1.86/0.99  --inst_learning_start                   3000
% 1.86/0.99  --inst_learning_factor                  2
% 1.86/0.99  --inst_start_prop_sim_after_learn       3
% 1.86/0.99  --inst_sel_renew                        solver
% 1.86/0.99  --inst_lit_activity_flag                true
% 1.86/0.99  --inst_restr_to_given                   false
% 1.86/0.99  --inst_activity_threshold               500
% 1.86/0.99  --inst_out_proof                        true
% 1.86/0.99  
% 1.86/0.99  ------ Resolution Options
% 1.86/0.99  
% 1.86/0.99  --resolution_flag                       false
% 1.86/0.99  --res_lit_sel                           adaptive
% 1.86/0.99  --res_lit_sel_side                      none
% 1.86/0.99  --res_ordering                          kbo
% 1.86/0.99  --res_to_prop_solver                    active
% 1.86/0.99  --res_prop_simpl_new                    false
% 1.86/0.99  --res_prop_simpl_given                  true
% 1.86/0.99  --res_passive_queue_type                priority_queues
% 1.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.86/0.99  --res_passive_queues_freq               [15;5]
% 1.86/0.99  --res_forward_subs                      full
% 1.86/0.99  --res_backward_subs                     full
% 1.86/0.99  --res_forward_subs_resolution           true
% 1.86/0.99  --res_backward_subs_resolution          true
% 1.86/0.99  --res_orphan_elimination                true
% 1.86/0.99  --res_time_limit                        2.
% 1.86/0.99  --res_out_proof                         true
% 1.86/0.99  
% 1.86/0.99  ------ Superposition Options
% 1.86/0.99  
% 1.86/0.99  --superposition_flag                    true
% 1.86/0.99  --sup_passive_queue_type                priority_queues
% 1.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.86/0.99  --demod_completeness_check              fast
% 1.86/0.99  --demod_use_ground                      true
% 1.86/0.99  --sup_to_prop_solver                    passive
% 1.86/0.99  --sup_prop_simpl_new                    true
% 1.86/0.99  --sup_prop_simpl_given                  true
% 1.86/0.99  --sup_fun_splitting                     false
% 1.86/0.99  --sup_smt_interval                      50000
% 1.86/0.99  
% 1.86/0.99  ------ Superposition Simplification Setup
% 1.86/0.99  
% 1.86/0.99  --sup_indices_passive                   []
% 1.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_full_bw                           [BwDemod]
% 1.86/0.99  --sup_immed_triv                        [TrivRules]
% 1.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_immed_bw_main                     []
% 1.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.86/0.99  
% 1.86/0.99  ------ Combination Options
% 1.86/0.99  
% 1.86/0.99  --comb_res_mult                         3
% 1.86/0.99  --comb_sup_mult                         2
% 1.86/0.99  --comb_inst_mult                        10
% 1.86/0.99  
% 1.86/0.99  ------ Debug Options
% 1.86/0.99  
% 1.86/0.99  --dbg_backtrace                         false
% 1.86/0.99  --dbg_dump_prop_clauses                 false
% 1.86/0.99  --dbg_dump_prop_clauses_file            -
% 1.86/0.99  --dbg_out_stat                          false
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  ------ Proving...
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  % SZS status Theorem for theBenchmark.p
% 1.86/0.99  
% 1.86/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.86/0.99  
% 1.86/0.99  fof(f1,axiom,(
% 1.86/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f12,plain,(
% 1.86/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.86/0.99    inference(ennf_transformation,[],[f1])).
% 1.86/0.99  
% 1.86/0.99  fof(f23,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.86/0.99    inference(nnf_transformation,[],[f12])).
% 1.86/0.99  
% 1.86/0.99  fof(f24,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.86/0.99    inference(rectify,[],[f23])).
% 1.86/0.99  
% 1.86/0.99  fof(f25,plain,(
% 1.86/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 1.86/0.99    introduced(choice_axiom,[])).
% 1.86/0.99  
% 1.86/0.99  fof(f26,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 1.86/0.99  
% 1.86/0.99  fof(f33,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f26])).
% 1.86/0.99  
% 1.86/0.99  fof(f5,axiom,(
% 1.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f18,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.99    inference(ennf_transformation,[],[f5])).
% 1.86/0.99  
% 1.86/0.99  fof(f40,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.86/0.99    inference(cnf_transformation,[],[f18])).
% 1.86/0.99  
% 1.86/0.99  fof(f8,conjecture,(
% 1.86/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f9,negated_conjecture,(
% 1.86/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 1.86/0.99    inference(negated_conjecture,[],[f8])).
% 1.86/0.99  
% 1.86/0.99  fof(f10,plain,(
% 1.86/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 1.86/0.99    inference(pure_predicate_removal,[],[f9])).
% 1.86/0.99  
% 1.86/0.99  fof(f21,plain,(
% 1.86/0.99    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 1.86/0.99    inference(ennf_transformation,[],[f10])).
% 1.86/0.99  
% 1.86/0.99  fof(f22,plain,(
% 1.86/0.99    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 1.86/0.99    inference(flattening,[],[f21])).
% 1.86/0.99  
% 1.86/0.99  fof(f29,plain,(
% 1.86/0.99    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK4,X4) != sK3 | ~r2_hidden(X4,sK1)) & r2_hidden(sK3,k2_relset_1(sK1,sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4))),
% 1.86/0.99    introduced(choice_axiom,[])).
% 1.86/0.99  
% 1.86/0.99  fof(f30,plain,(
% 1.86/0.99    ! [X4] : (k1_funct_1(sK4,X4) != sK3 | ~r2_hidden(X4,sK1)) & r2_hidden(sK3,k2_relset_1(sK1,sK2,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_1(sK4)),
% 1.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f22,f29])).
% 1.86/0.99  
% 1.86/0.99  fof(f44,plain,(
% 1.86/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.86/0.99    inference(cnf_transformation,[],[f30])).
% 1.86/0.99  
% 1.86/0.99  fof(f2,axiom,(
% 1.86/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f13,plain,(
% 1.86/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.86/0.99    inference(ennf_transformation,[],[f2])).
% 1.86/0.99  
% 1.86/0.99  fof(f35,plain,(
% 1.86/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f13])).
% 1.86/0.99  
% 1.86/0.99  fof(f7,axiom,(
% 1.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f20,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.99    inference(ennf_transformation,[],[f7])).
% 1.86/0.99  
% 1.86/0.99  fof(f42,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.86/0.99    inference(cnf_transformation,[],[f20])).
% 1.86/0.99  
% 1.86/0.99  fof(f45,plain,(
% 1.86/0.99    r2_hidden(sK3,k2_relset_1(sK1,sK2,sK4))),
% 1.86/0.99    inference(cnf_transformation,[],[f30])).
% 1.86/0.99  
% 1.86/0.99  fof(f6,axiom,(
% 1.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f11,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.86/0.99    inference(pure_predicate_removal,[],[f6])).
% 1.86/0.99  
% 1.86/0.99  fof(f19,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.86/0.99    inference(ennf_transformation,[],[f11])).
% 1.86/0.99  
% 1.86/0.99  fof(f41,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.86/0.99    inference(cnf_transformation,[],[f19])).
% 1.86/0.99  
% 1.86/0.99  fof(f3,axiom,(
% 1.86/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f14,plain,(
% 1.86/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.86/0.99    inference(ennf_transformation,[],[f3])).
% 1.86/0.99  
% 1.86/0.99  fof(f15,plain,(
% 1.86/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.86/0.99    inference(flattening,[],[f14])).
% 1.86/0.99  
% 1.86/0.99  fof(f36,plain,(
% 1.86/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f15])).
% 1.86/0.99  
% 1.86/0.99  fof(f32,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f26])).
% 1.86/0.99  
% 1.86/0.99  fof(f4,axiom,(
% 1.86/0.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.86/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.86/0.99  
% 1.86/0.99  fof(f16,plain,(
% 1.86/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.86/0.99    inference(ennf_transformation,[],[f4])).
% 1.86/0.99  
% 1.86/0.99  fof(f17,plain,(
% 1.86/0.99    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.86/0.99    inference(flattening,[],[f16])).
% 1.86/0.99  
% 1.86/0.99  fof(f27,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.86/0.99    inference(nnf_transformation,[],[f17])).
% 1.86/0.99  
% 1.86/0.99  fof(f28,plain,(
% 1.86/0.99    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.86/0.99    inference(flattening,[],[f27])).
% 1.86/0.99  
% 1.86/0.99  fof(f38,plain,(
% 1.86/0.99    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f28])).
% 1.86/0.99  
% 1.86/0.99  fof(f43,plain,(
% 1.86/0.99    v1_funct_1(sK4)),
% 1.86/0.99    inference(cnf_transformation,[],[f30])).
% 1.86/0.99  
% 1.86/0.99  fof(f46,plain,(
% 1.86/0.99    ( ! [X4] : (k1_funct_1(sK4,X4) != sK3 | ~r2_hidden(X4,sK1)) )),
% 1.86/0.99    inference(cnf_transformation,[],[f30])).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1,plain,
% 1.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.86/0.99      | r2_hidden(sK0(X0,X2,X1),X2)
% 1.86/0.99      | ~ v1_relat_1(X1) ),
% 1.86/0.99      inference(cnf_transformation,[],[f33]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_9,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.99      | v1_relat_1(X0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_14,negated_conjecture,
% 1.86/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.86/0.99      inference(cnf_transformation,[],[f44]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_225,plain,
% 1.86/0.99      ( v1_relat_1(X0)
% 1.86/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.86/0.99      | sK4 != X0 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_226,plain,
% 1.86/0.99      ( v1_relat_1(sK4)
% 1.86/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_225]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_373,plain,
% 1.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.86/0.99      | r2_hidden(sK0(X0,X2,X1),X2)
% 1.86/0.99      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.86/0.99      | sK4 != X1 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_226]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_374,plain,
% 1.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 1.86/0.99      | r2_hidden(sK0(X0,X1,sK4),X1)
% 1.86/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_373]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_524,plain,
% 1.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 1.86/0.99      | r2_hidden(sK0(X0,X1,sK4),X1)
% 1.86/0.99      | ~ sP3_iProver_split ),
% 1.86/0.99      inference(splitting,
% 1.86/0.99                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 1.86/0.99                [c_374]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_910,plain,
% 1.86/0.99      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.86/0.99      | r2_hidden(sK0(X0,X1,sK4),X1) = iProver_top
% 1.86/0.99      | sP3_iProver_split != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_525,plain,
% 1.86/0.99      ( sP3_iProver_split | sP1_iProver_split ),
% 1.86/0.99      inference(splitting,
% 1.86/0.99                [splitting(split),new_symbols(definition,[])],
% 1.86/0.99                [c_374]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_575,plain,
% 1.86/0.99      ( sP3_iProver_split = iProver_top
% 1.86/0.99      | sP1_iProver_split = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_576,plain,
% 1.86/0.99      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.86/0.99      | r2_hidden(sK0(X0,X1,sK4),X1) = iProver_top
% 1.86/0.99      | sP3_iProver_split != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_537,plain,( X0 = X0 ),theory(equality) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1077,plain,
% 1.86/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_537]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_4,plain,
% 1.86/0.99      ( ~ v1_relat_1(X0)
% 1.86/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 1.86/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_410,plain,
% 1.86/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.86/0.99      | k2_relat_1(k7_relat_1(X2,X3)) = k9_relat_1(X2,X3)
% 1.86/0.99      | sK4 != X2 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_226]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_411,plain,
% 1.86/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.86/0.99      | k2_relat_1(k7_relat_1(sK4,X2)) = k9_relat_1(sK4,X2) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_410]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_520,plain,
% 1.86/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.86/0.99      | ~ sP1_iProver_split ),
% 1.86/0.99      inference(splitting,
% 1.86/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.86/0.99                [c_411]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1078,plain,
% 1.86/0.99      ( ~ sP1_iProver_split
% 1.86/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.86/0.99      inference(instantiation,[status(thm)],[c_520]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1081,plain,
% 1.86/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.86/0.99      | sP1_iProver_split != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1078]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1287,plain,
% 1.86/0.99      ( r2_hidden(sK0(X0,X1,sK4),X1) = iProver_top
% 1.86/0.99      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_910,c_575,c_576,c_1077,c_1081]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1288,plain,
% 1.86/0.99      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.86/0.99      | r2_hidden(sK0(X0,X1,sK4),X1) = iProver_top ),
% 1.86/0.99      inference(renaming,[status(thm)],[c_1287]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_11,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.86/0.99      inference(cnf_transformation,[],[f42]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_216,plain,
% 1.86/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.86/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.86/0.99      | sK4 != X2 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_217,plain,
% 1.86/0.99      ( k2_relset_1(X0,X1,sK4) = k2_relat_1(sK4)
% 1.86/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_216]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1076,plain,
% 1.86/0.99      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 1.86/0.99      inference(equality_resolution,[status(thm)],[c_217]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_13,negated_conjecture,
% 1.86/0.99      ( r2_hidden(sK3,k2_relset_1(sK1,sK2,sK4)) ),
% 1.86/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_927,plain,
% 1.86/0.99      ( r2_hidden(sK3,k2_relset_1(sK1,sK2,sK4)) = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1094,plain,
% 1.86/0.99      ( r2_hidden(sK3,k2_relat_1(sK4)) = iProver_top ),
% 1.86/0.99      inference(demodulation,[status(thm)],[c_1076,c_927]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_10,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.99      | v4_relat_1(X0,X1) ),
% 1.86/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_5,plain,
% 1.86/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 1.86/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_187,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.99      | ~ v1_relat_1(X0)
% 1.86/0.99      | k7_relat_1(X0,X1) = X0 ),
% 1.86/0.99      inference(resolution,[status(thm)],[c_10,c_5]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_191,plain,
% 1.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.86/0.99      | k7_relat_1(X0,X1) = X0 ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_187,c_10,c_9,c_5]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_207,plain,
% 1.86/0.99      ( k7_relat_1(X0,X1) = X0
% 1.86/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.86/0.99      | sK4 != X0 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_191,c_14]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_208,plain,
% 1.86/0.99      ( k7_relat_1(sK4,X0) = sK4
% 1.86/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_207]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1073,plain,
% 1.86/0.99      ( k7_relat_1(sK4,sK1) = sK4 ),
% 1.86/0.99      inference(equality_resolution,[status(thm)],[c_208]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_519,plain,
% 1.86/0.99      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0)
% 1.86/0.99      | ~ sP0_iProver_split ),
% 1.86/0.99      inference(splitting,
% 1.86/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.86/0.99                [c_411]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_905,plain,
% 1.86/0.99      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0)
% 1.86/0.99      | sP0_iProver_split != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_521,plain,
% 1.86/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 1.86/0.99      inference(splitting,
% 1.86/0.99                [splitting(split),new_symbols(definition,[])],
% 1.86/0.99                [c_411]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1115,plain,
% 1.86/0.99      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_905,c_521,c_519,c_1077,c_1078]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1119,plain,
% 1.86/0.99      ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1073,c_1115]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_2,plain,
% 1.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.86/0.99      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 1.86/0.99      | ~ v1_relat_1(X1) ),
% 1.86/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_358,plain,
% 1.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.86/0.99      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 1.86/0.99      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.86/0.99      | sK4 != X1 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_226]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_359,plain,
% 1.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 1.86/0.99      | r2_hidden(k4_tarski(sK0(X0,X1,sK4),X0),sK4)
% 1.86/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_358]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_526,plain,
% 1.86/0.99      ( ~ r2_hidden(X0,k9_relat_1(sK4,X1))
% 1.86/0.99      | r2_hidden(k4_tarski(sK0(X0,X1,sK4),X0),sK4)
% 1.86/0.99      | ~ sP4_iProver_split ),
% 1.86/0.99      inference(splitting,
% 1.86/0.99                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 1.86/0.99                [c_359]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_913,plain,
% 1.86/0.99      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.86/0.99      | r2_hidden(k4_tarski(sK0(X0,X1,sK4),X0),sK4) = iProver_top
% 1.86/0.99      | sP4_iProver_split != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_527,plain,
% 1.86/0.99      ( sP4_iProver_split | sP1_iProver_split ),
% 1.86/0.99      inference(splitting,
% 1.86/0.99                [splitting(split),new_symbols(definition,[])],
% 1.86/0.99                [c_359]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_580,plain,
% 1.86/0.99      ( sP4_iProver_split = iProver_top
% 1.86/0.99      | sP1_iProver_split = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_581,plain,
% 1.86/0.99      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.86/0.99      | r2_hidden(k4_tarski(sK0(X0,X1,sK4),X0),sK4) = iProver_top
% 1.86/0.99      | sP4_iProver_split != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1392,plain,
% 1.86/0.99      ( r2_hidden(k4_tarski(sK0(X0,X1,sK4),X0),sK4) = iProver_top
% 1.86/0.99      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_913,c_580,c_581,c_1077,c_1081]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1393,plain,
% 1.86/0.99      ( r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top
% 1.86/0.99      | r2_hidden(k4_tarski(sK0(X0,X1,sK4),X0),sK4) = iProver_top ),
% 1.86/0.99      inference(renaming,[status(thm)],[c_1392]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_7,plain,
% 1.86/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 1.86/0.99      | ~ v1_funct_1(X2)
% 1.86/0.99      | ~ v1_relat_1(X2)
% 1.86/0.99      | k1_funct_1(X2,X0) = X1 ),
% 1.86/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_15,negated_conjecture,
% 1.86/0.99      ( v1_funct_1(sK4) ),
% 1.86/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_274,plain,
% 1.86/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 1.86/0.99      | ~ v1_relat_1(X2)
% 1.86/0.99      | k1_funct_1(X2,X0) = X1
% 1.86/0.99      | sK4 != X2 ),
% 1.86/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_275,plain,
% 1.86/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 1.86/0.99      | ~ v1_relat_1(sK4)
% 1.86/0.99      | k1_funct_1(sK4,X0) = X1 ),
% 1.86/0.99      inference(unflattening,[status(thm)],[c_274]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_301,plain,
% 1.86/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 1.86/0.99      | k1_funct_1(sK4,X0) = X1
% 1.86/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.86/0.99      inference(resolution,[status(thm)],[c_226,c_275]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_534,plain,
% 1.86/0.99      ( ~ r2_hidden(k4_tarski(X0,X1),sK4)
% 1.86/0.99      | k1_funct_1(sK4,X0) = X1
% 1.86/0.99      | ~ sP8_iProver_split ),
% 1.86/0.99      inference(splitting,
% 1.86/0.99                [splitting(split),new_symbols(definition,[sP8_iProver_split])],
% 1.86/0.99                [c_301]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_925,plain,
% 1.86/0.99      ( k1_funct_1(sK4,X0) = X1
% 1.86/0.99      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 1.86/0.99      | sP8_iProver_split != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_535,plain,
% 1.86/0.99      ( sP8_iProver_split | sP1_iProver_split ),
% 1.86/0.99      inference(splitting,
% 1.86/0.99                [splitting(split),new_symbols(definition,[])],
% 1.86/0.99                [c_301]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_600,plain,
% 1.86/0.99      ( sP8_iProver_split = iProver_top
% 1.86/0.99      | sP1_iProver_split = iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_601,plain,
% 1.86/0.99      ( k1_funct_1(sK4,X0) = X1
% 1.86/0.99      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 1.86/0.99      | sP8_iProver_split != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1267,plain,
% 1.86/0.99      ( r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top
% 1.86/0.99      | k1_funct_1(sK4,X0) = X1 ),
% 1.86/0.99      inference(global_propositional_subsumption,
% 1.86/0.99                [status(thm)],
% 1.86/0.99                [c_925,c_600,c_601,c_1077,c_1081]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1268,plain,
% 1.86/0.99      ( k1_funct_1(sK4,X0) = X1
% 1.86/0.99      | r2_hidden(k4_tarski(X0,X1),sK4) != iProver_top ),
% 1.86/0.99      inference(renaming,[status(thm)],[c_1267]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1401,plain,
% 1.86/0.99      ( k1_funct_1(sK4,sK0(X0,X1,sK4)) = X0
% 1.86/0.99      | r2_hidden(X0,k9_relat_1(sK4,X1)) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1393,c_1268]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1597,plain,
% 1.86/0.99      ( k1_funct_1(sK4,sK0(X0,sK1,sK4)) = X0
% 1.86/0.99      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1119,c_1401]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1682,plain,
% 1.86/0.99      ( k1_funct_1(sK4,sK0(sK3,sK1,sK4)) = sK3 ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1094,c_1597]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_12,negated_conjecture,
% 1.86/0.99      ( ~ r2_hidden(X0,sK1) | k1_funct_1(sK4,X0) != sK3 ),
% 1.86/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_928,plain,
% 1.86/0.99      ( k1_funct_1(sK4,X0) != sK3 | r2_hidden(X0,sK1) != iProver_top ),
% 1.86/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1694,plain,
% 1.86/0.99      ( r2_hidden(sK0(sK3,sK1,sK4),sK1) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1682,c_928]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1761,plain,
% 1.86/0.99      ( r2_hidden(sK3,k9_relat_1(sK4,sK1)) != iProver_top ),
% 1.86/0.99      inference(superposition,[status(thm)],[c_1288,c_1694]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(c_1762,plain,
% 1.86/0.99      ( r2_hidden(sK3,k2_relat_1(sK4)) != iProver_top ),
% 1.86/0.99      inference(light_normalisation,[status(thm)],[c_1761,c_1119]) ).
% 1.86/0.99  
% 1.86/0.99  cnf(contradiction,plain,
% 1.86/0.99      ( $false ),
% 1.86/0.99      inference(minisat,[status(thm)],[c_1762,c_1094]) ).
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.86/0.99  
% 1.86/0.99  ------                               Statistics
% 1.86/0.99  
% 1.86/0.99  ------ General
% 1.86/0.99  
% 1.86/0.99  abstr_ref_over_cycles:                  0
% 1.86/0.99  abstr_ref_under_cycles:                 0
% 1.86/0.99  gc_basic_clause_elim:                   0
% 1.86/0.99  forced_gc_time:                         0
% 1.86/0.99  parsing_time:                           0.007
% 1.86/0.99  unif_index_cands_time:                  0.
% 1.86/0.99  unif_index_add_time:                    0.
% 1.86/0.99  orderings_time:                         0.
% 1.86/0.99  out_proof_time:                         0.008
% 1.86/0.99  total_time:                             0.08
% 1.86/0.99  num_of_symbols:                         59
% 1.86/0.99  num_of_terms:                           1234
% 1.86/0.99  
% 1.86/0.99  ------ Preprocessing
% 1.86/0.99  
% 1.86/0.99  num_of_splits:                          16
% 1.86/0.99  num_of_split_atoms:                     9
% 1.86/0.99  num_of_reused_defs:                     7
% 1.86/0.99  num_eq_ax_congr_red:                    22
% 1.86/0.99  num_of_sem_filtered_clauses:            1
% 1.86/0.99  num_of_subtypes:                        0
% 1.86/0.99  monotx_restored_types:                  0
% 1.86/0.99  sat_num_of_epr_types:                   0
% 1.86/0.99  sat_num_of_non_cyclic_types:            0
% 1.86/0.99  sat_guarded_non_collapsed_types:        0
% 1.86/0.99  num_pure_diseq_elim:                    0
% 1.86/0.99  simp_replaced_by:                       0
% 1.86/0.99  res_preprocessed:                       97
% 1.86/0.99  prep_upred:                             0
% 1.86/0.99  prep_unflattend:                        11
% 1.86/0.99  smt_new_axioms:                         0
% 1.86/0.99  pred_elim_cands:                        1
% 1.86/0.99  pred_elim:                              4
% 1.86/0.99  pred_elim_cl:                           4
% 1.86/0.99  pred_elim_cycles:                       6
% 1.86/0.99  merged_defs:                            0
% 1.86/0.99  merged_defs_ncl:                        0
% 1.86/0.99  bin_hyper_res:                          0
% 1.86/0.99  prep_cycles:                            4
% 1.86/0.99  pred_elim_time:                         0.005
% 1.86/0.99  splitting_time:                         0.
% 1.86/0.99  sem_filter_time:                        0.
% 1.86/0.99  monotx_time:                            0.
% 1.86/0.99  subtype_inf_time:                       0.
% 1.86/0.99  
% 1.86/0.99  ------ Problem properties
% 1.86/0.99  
% 1.86/0.99  clauses:                                28
% 1.86/0.99  conjectures:                            2
% 1.86/0.99  epr:                                    8
% 1.86/0.99  horn:                                   20
% 1.86/0.99  ground:                                 9
% 1.86/0.99  unary:                                  1
% 1.86/0.99  binary:                                 20
% 1.86/0.99  lits:                                   63
% 1.86/0.99  lits_eq:                                15
% 1.86/0.99  fd_pure:                                0
% 1.86/0.99  fd_pseudo:                              0
% 1.86/0.99  fd_cond:                                0
% 1.86/0.99  fd_pseudo_cond:                         1
% 1.86/0.99  ac_symbols:                             0
% 1.86/0.99  
% 1.86/0.99  ------ Propositional Solver
% 1.86/0.99  
% 1.86/0.99  prop_solver_calls:                      29
% 1.86/0.99  prop_fast_solver_calls:                 615
% 1.86/0.99  smt_solver_calls:                       0
% 1.86/0.99  smt_fast_solver_calls:                  0
% 1.86/0.99  prop_num_of_clauses:                    505
% 1.86/0.99  prop_preprocess_simplified:             2842
% 1.86/0.99  prop_fo_subsumed:                       18
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
% 1.86/0.99  inst_num_of_clauses:                    146
% 1.86/0.99  inst_num_in_passive:                    22
% 1.86/0.99  inst_num_in_active:                     124
% 1.86/0.99  inst_num_in_unprocessed:                0
% 1.86/0.99  inst_num_of_loops:                      150
% 1.86/0.99  inst_num_of_learning_restarts:          0
% 1.86/0.99  inst_num_moves_active_passive:          19
% 1.86/0.99  inst_lit_activity:                      0
% 1.86/0.99  inst_lit_activity_moves:                0
% 1.86/0.99  inst_num_tautologies:                   0
% 1.86/0.99  inst_num_prop_implied:                  0
% 1.86/0.99  inst_num_existing_simplified:           0
% 1.86/0.99  inst_num_eq_res_simplified:             0
% 1.86/0.99  inst_num_child_elim:                    0
% 1.86/0.99  inst_num_of_dismatching_blockings:      16
% 1.86/0.99  inst_num_of_non_proper_insts:           125
% 1.86/0.99  inst_num_of_duplicates:                 0
% 1.86/0.99  inst_inst_num_from_inst_to_res:         0
% 1.86/0.99  inst_dismatching_checking_time:         0.
% 1.86/0.99  
% 1.86/0.99  ------ Resolution
% 1.86/0.99  
% 1.86/0.99  res_num_of_clauses:                     0
% 1.86/0.99  res_num_in_passive:                     0
% 1.86/0.99  res_num_in_active:                      0
% 1.86/0.99  res_num_of_loops:                       101
% 1.86/0.99  res_forward_subset_subsumed:            36
% 1.86/0.99  res_backward_subset_subsumed:           4
% 1.86/0.99  res_forward_subsumed:                   0
% 1.86/0.99  res_backward_subsumed:                  0
% 1.86/0.99  res_forward_subsumption_resolution:     1
% 1.86/0.99  res_backward_subsumption_resolution:    0
% 1.86/0.99  res_clause_to_clause_subsumption:       37
% 1.86/0.99  res_orphan_elimination:                 0
% 1.86/0.99  res_tautology_del:                      28
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
% 1.86/0.99  sup_num_of_clauses:                     34
% 1.86/0.99  sup_num_in_active:                      28
% 1.86/0.99  sup_num_in_passive:                     6
% 1.86/0.99  sup_num_of_loops:                       28
% 1.86/0.99  sup_fw_superposition:                   8
% 1.86/0.99  sup_bw_superposition:                   6
% 1.86/0.99  sup_immediate_simplified:               1
% 1.86/0.99  sup_given_eliminated:                   0
% 1.86/0.99  comparisons_done:                       0
% 1.86/0.99  comparisons_avoided:                    0
% 1.86/0.99  
% 1.86/0.99  ------ Simplifications
% 1.86/0.99  
% 1.86/0.99  
% 1.86/0.99  sim_fw_subset_subsumed:                 0
% 1.86/0.99  sim_bw_subset_subsumed:                 0
% 1.86/0.99  sim_fw_subsumed:                        0
% 1.86/0.99  sim_bw_subsumed:                        0
% 1.86/0.99  sim_fw_subsumption_res:                 0
% 1.86/0.99  sim_bw_subsumption_res:                 0
% 1.86/0.99  sim_tautology_del:                      1
% 1.86/0.99  sim_eq_tautology_del:                   1
% 1.86/0.99  sim_eq_res_simp:                        0
% 1.86/0.99  sim_fw_demodulated:                     0
% 1.86/0.99  sim_bw_demodulated:                     1
% 1.86/0.99  sim_light_normalised:                   1
% 1.86/0.99  sim_joinable_taut:                      0
% 1.86/0.99  sim_joinable_simp:                      0
% 1.86/0.99  sim_ac_normalised:                      0
% 1.86/0.99  sim_smt_subsumption:                    0
% 1.86/0.99  
%------------------------------------------------------------------------------
